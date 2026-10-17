#!/usr/bin/env python3
"""
Immoweb Auto-Monitor & Apply
Polls Immoweb every 5–8 min for new studio/1BR listings in south Brussels,
and sends the contact form on each new one, logged in with your Immoweb account.

Usage:
  python monitor.py                # monitor + apply (visible Chrome window)
  python monitor.py --dry-run      # search only, don't open a browser or apply
  python monitor.py --no-send      # fill the contact form but never click "Send"
  python monitor.py --test-url URL --no-send   # try the form on one listing, then exit

Notes:
  - Immoweb is behind Cloudflare. Headless Chromium gets a "Just a moment..." page,
    so this uses your installed Google Chrome in a visible window with a persistent
    profile (.browser-profile/) that keeps the Cloudflare clearance and login session.
  - The first run only records the listings that already exist; it applies to
    listings that appear after that (use --apply-existing to override).
"""

import argparse
import getpass
import json
import os
import random
import re
import sys
import time
from datetime import date, datetime, timedelta
from pathlib import Path

import requests
from dotenv import load_dotenv, set_key
from playwright.sync_api import TimeoutError as PWTimeout
from playwright.sync_api import sync_playwright

# ─── CONFIG ───────────────────────────────────────────────────────────────────

POSTAL_CODES = [
    "BE-1050",  # Ixelles / Elsene
    "BE-1190",  # Forest / Vorst
    "BE-1060",  # Saint-Gilles / Sint-Gillis
    "BE-1040",  # Etterbeek
    "BE-1200",  # Woluwe-Saint-Lambert
    "BE-1150",  # Woluwe-Saint-Pierre
    "BE-1180",  # Uccle / Ukkel
]

MAX_PRICE = 1300
MIN_BEDROOMS = 0  # 0 = studio
MAX_BEDROOMS = 1
EXCLUDED_SUBTYPES = {"KOT"}  # student rooms
AVAILABLE_ON = date(2026, 12, 1)  # only apply if the listing's availability date is exactly this day
APPLY_IF_AVAILABILITY_UNKNOWN = False  # listings with no availability date set
POLL_INTERVAL_MINUTES = (5, 8)  # random wait between checks, in minutes
QUIET_HOURS = (1, 7)  # no checks from 01:00 until 07:00 local time; None to poll all night
BACKOFF_MINUTES = 30  # wait after a 403/429; doubles on each consecutive block
MAX_BACKOFF_MINUTES = 240
DELAY_BETWEEN_APPLICATIONS_S = 20

# Paths
DIR = Path(__file__).parent
STATE_FILE = DIR / "state.json"
ENV_FILE = DIR / ".env"
PROFILE_DIR = DIR / ".browser-profile"
SCREENSHOT_DIR = DIR / "screenshots"

HOME_URL = "https://www.immoweb.be/en"

# ─── APPLICATION MESSAGE ──────────────────────────────────────────────────────

# Immoweb's message box has maxlength=500 — keep it under that (checked at startup).
MESSAGE_MAX_LENGTH = 500
APPLICATION_MESSAGE = """\
Hello,

I am very interested in your apartment and would love to visit it.

I am a professional based in Brussels with a stable income, a quiet and responsible tenant, \
and can provide pay slips and references.

Would a 1-year rental contract be possible? I know 3 years is the default, but I would \
appreciate the flexibility and am open to discussing terms.

Could you let me know about the contract length and your availability for a viewing?

Thank you, kind regards,
{first_name}\
"""

# ─── SEARCH API ───────────────────────────────────────────────────────────────
# The search-results URL returns JSON when asked with Accept: application/json.

SEARCH_URL = "https://www.immoweb.be/en/search-results/apartment/for-rent"
SEARCH_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/129.0.0.0 Safari/537.36"
    ),
    "Accept": "application/json",
    "Accept-Language": "en-GB,en;q=0.9",
}


class RateLimited(Exception):
    """Immoweb answered 403/429: stop hitting it for a while."""

    def __init__(self, status: int, retry_after_s: int | None = None):
        super().__init__(f"HTTP {status}")
        self.retry_after_s = retry_after_s


def _get(url: str, **kwargs) -> requests.Response:
    resp = requests.get(url, timeout=30, **kwargs)
    if resp.status_code in (403, 429):
        retry_after = resp.headers.get("Retry-After", "")
        raise RateLimited(resp.status_code, int(retry_after) if retry_after.isdigit() else None)
    resp.raise_for_status()
    return resp


def fetch_listings() -> list[dict]:
    params = {
        "countries": "BE",
        "postalCodes": ",".join(POSTAL_CODES),
        "maxPrice": MAX_PRICE,
        "minBedroomCount": MIN_BEDROOMS,
        "maxBedroomCount": MAX_BEDROOMS,
        "orderBy": "newest",
        "page": 1,
    }
    data = _get(SEARCH_URL, params=params, headers=SEARCH_HEADERS).json()

    listings = []
    for r in data.get("results", []):
        prop = r.get("property") or {}
        if prop.get("subtype") in EXCLUDED_SUBTYPES:
            continue
        loc = prop.get("location") or {}
        rental = (r.get("transaction") or {}).get("rental") or {}
        price = rental.get("monthlyRentalPrice") or (r.get("price") or {}).get("mainValue")
        listings.append(
            {
                "id": str(r.get("id", "")),
                "title": prop.get("title") or "No title",
                "price": price,
                "charges": rental.get("monthlyRentalCosts"),
                "locality": loc.get("locality", ""),
                "postal_code": loc.get("postalCode", ""),
                "bedrooms": prop.get("bedroomCount") or 0,
                "surface": prop.get("netHabitableSurface"),
                "url": _build_url(r),
            }
        )
    return listings


def _build_url(r: dict) -> str:
    # Immoweb redirects to the canonical slug, so the locality part only needs to be plausible.
    loc = (r.get("property") or {}).get("location") or {}
    locality = (loc.get("locality") or "brussels").lower().replace(" ", "-").replace("'", "")
    postal = loc.get("postalCode") or "1000"
    return f"https://www.immoweb.be/en/classified/apartment/for-rent/{locality}/{postal}/{r.get('id', '')}"


def fetch_availability(listing: dict) -> date | str | None:
    """Availability isn't in the search results, but the listing page embeds the classified JSON
    with transaction.availabilityDate ("YYYY-MM-DD") or availabilityPeriodType ("IMMEDIATELY").
    Returns a date, "IMMEDIATELY", or None if the landlord didn't set either."""
    headers = {**SEARCH_HEADERS, "Accept": "text/html"}
    html = _get(listing["url"], headers=headers).text
    if "just a moment" in html[:5000].lower():
        raise RuntimeError("Cloudflare challenge on listing page")
    m = re.search(r'"availabilityDate":"(\d{4}-\d{2}-\d{2})"', html)
    if m:
        return date.fromisoformat(m.group(1))
    m = re.search(r'"availabilityPeriodType":"([A-Z_]+)"', html)
    return m.group(1) if m else None


def availability_ok(avail: date | str | None) -> bool:
    if isinstance(avail, date):
        return avail == AVAILABLE_ON
    if avail is None:
        return APPLY_IF_AVAILABILITY_UNKNOWN
    return False  # IMMEDIATELY or other period types


# ─── STATE ────────────────────────────────────────────────────────────────────


def load_state() -> dict:
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text())
    return {"seen": [], "applied": [], "failed": [], "skipped": []}


def save_state(state: dict) -> None:
    STATE_FILE.write_text(json.dumps(state, indent=2))


# ─── CREDENTIALS & PROFILE ────────────────────────────────────────────────────


def ask_credentials() -> tuple[str, str]:
    """Always ask at startup. The password is kept in memory only, never written to disk."""
    load_dotenv(ENV_FILE)
    default_email = os.environ.get("IMMOWEB_EMAIL", "").strip()

    prompt = f"Immoweb email [{default_email}]: " if default_email else "Immoweb email: "
    email = input(prompt).strip() or default_email
    while not email:
        email = input("Immoweb email: ").strip()

    password = ""
    while not password:
        password = getpass.getpass("Immoweb password: ")

    _save_env("IMMOWEB_EMAIL", email)
    return email, password


def load_profile() -> dict:
    """Name/phone used in the contact form. Asked once, then remembered in .env."""
    load_dotenv(ENV_FILE)
    profile = {}
    for key, label, required in [
        ("FIRST_NAME", "First name", True),
        ("LAST_NAME", "Last name", True),
        ("PHONE", "Phone number (optional, e.g. +32470123456)", False),
    ]:
        value = os.environ.get(key, "").strip()
        if not value and key not in os.environ:
            value = input(f"{label}: ").strip()
            while required and not value:
                value = input(f"{label}: ").strip()
            _save_env(key, value)
        profile[key.lower()] = value
    return profile


def _save_env(key: str, value: str) -> None:
    ENV_FILE.touch(mode=0o600, exist_ok=True)
    set_key(str(ENV_FILE), key, value, quote_mode="never")
    os.environ[key] = value


# ─── BROWSER SESSION ──────────────────────────────────────────────────────────


class ImmowebSession:
    def __init__(self, email: str, password: str, profile: dict, headless: bool = False):
        self.email = email
        self.password = password
        self.profile = profile
        self.headless = headless
        self._pw = None
        self._context = None
        self.page = None

    def __enter__(self):
        self._pw = sync_playwright().start()
        self._context = self._pw.chromium.launch_persistent_context(
            str(PROFILE_DIR),
            channel="chrome",  # real Chrome passes Cloudflare; bundled Chromium doesn't
            headless=self.headless,
            locale="en-GB",
            viewport={"width": 1280, "height": 900},
            args=["--disable-blink-features=AutomationControlled"],
        )
        self.page = self._context.pages[0] if self._context.pages else self._context.new_page()
        return self

    def __exit__(self, *_):
        if self._context:
            self._context.close()
        if self._pw:
            self._pw.stop()

    # ── helpers ──

    def _goto(self, url: str) -> None:
        self.page.goto(url, wait_until="domcontentloaded", timeout=45000)
        self._wait_for_cloudflare()
        self._accept_cookies()
        self._dismiss_preferences_popup()  # "Later" may bring it back on a later page load

    def _wait_for_cloudflare(self, timeout_s: int = 180) -> None:
        """Cloudflare shows 'Just a moment...' first. Usually clears by itself in real Chrome;
        if a checkbox appears, tick it in the browser window."""
        deadline = time.time() + timeout_s
        warned = False
        while "just a moment" in self.page.title().lower():
            if time.time() > deadline:
                raise RuntimeError("Stuck on Cloudflare challenge page")
            if not warned and time.time() > deadline - timeout_s + 15:
                log("  Cloudflare check showing — tick the box in the browser window if there is one.")
                warned = True
            self.page.wait_for_timeout(1000)

    def _accept_cookies(self) -> None:
        # Usercentrics banner, rendered in the #usercentrics-root shadow DOM (Playwright pierces it).
        btn = self.page.locator('[data-testid="uc-accept-all-button"]')
        try:
            btn.wait_for(state="visible", timeout=6000)
            btn.click()
            log("  Accepted cookie banner.")
        except PWTimeout:
            pass  # already accepted (persisted in profile) or not shown

    def screenshot(self, name: str) -> Path:
        SCREENSHOT_DIR.mkdir(exist_ok=True)
        path = SCREENSHOT_DIR / f"{datetime.now():%Y%m%d-%H%M%S}-{name}.png"
        try:
            self.page.screenshot(path=str(path), full_page=False)
        except Exception:
            pass
        return path

    # ── login ──

    def _dismiss_preferences_popup(self, timeout_ms: int = 0) -> None:
        # After login Immoweb shows a "Before continuing..." e-mail/phone subscription dialog.
        # "Later" closes it without opting in to anything.
        later = self.page.locator('button:text-is("Later"), a:text-is("Later")').first
        try:
            if timeout_ms:
                later.wait_for(state="visible", timeout=timeout_ms)
            elif not later.is_visible():
                return
            later.click()
            later.wait_for(state="hidden", timeout=5000)
            log("  Skipped subscription preferences popup.")
        except PWTimeout:
            pass  # not shown

    def is_logged_in(self, timeout_ms: int = 10000) -> bool:
        # Logged out: a single button#myImmowebMenu labelled "Log in".
        # Logged in: #myImmowebMenu becomes a dropdown (div + button share the id) with a "Log out" link.
        try:
            self.page.locator("#myImmowebMenu").first.wait_for(state="attached", timeout=timeout_ms)
            self.page.locator('#myImmowebMenu a[href*="/logout"]').wait_for(state="attached", timeout=3000)
        except PWTimeout:
            return False
        return True

    def login(self) -> bool:
        log("Opening Immoweb...")
        self._goto(HOME_URL)

        if self.is_logged_in():
            log("Already logged in (session restored from browser profile).")
            return True

        log("Opening login dialog...")
        self.page.locator("#myImmowebMenu").click()
        email_input = self.page.locator('input[name="login-email"]')
        try:
            email_input.wait_for(state="visible", timeout=10000)
        except PWTimeout:
            log(f"  Login dialog did not open. Screenshot: {self.screenshot('login-dialog')}")
            return False

        email_input.fill(self.email)
        self.page.locator('input[name="login-password"]').fill(self.password)
        email_input.locator("xpath=ancestor::form").locator('button[type="submit"]').click()

        # Dialog closes on success; on failure it stays open with an error.
        try:
            email_input.wait_for(state="hidden", timeout=20000)
        except PWTimeout:
            log(f"  Login dialog still open — wrong credentials or extra verification. "
                f"Screenshot: {self.screenshot('login-failed')}")
            return False

        self._dismiss_preferences_popup(timeout_ms=10000)
        if not self.is_logged_in():
            log(f"  Login dialog closed but header still says 'Log in'. "
                f"Screenshot: {self.screenshot('login-unverified')}")
            return False
        return True

    # ── apply ──

    def apply_to_listing(self, listing: dict, send: bool = True) -> bool:
        page = self.page
        try:
            self._goto(listing["url"])
        except Exception as e:
            log(f"  Could not load listing page: {e}")
            return False

        # The listing page has two contact forms; the bottom one (with "Send message"
        # button.sendMyRequestButton) shows the message box and "Schedule a visit" directly.
        form = page.locator("form.customer-card__form:has(button.sendMyRequestButton)").first
        try:
            form.wait_for(state="attached", timeout=15000)
            form.scroll_into_view_if_needed()
        except PWTimeout:
            log(f"  No contact form on listing {listing['id']} (removed, or agency-only contact). "
                f"Screenshot: {self.screenshot(listing['id'] + '-noform')}")
            return False

        try:
            form.locator('input[name="firstName"]').fill(self.profile["first_name"])
            form.locator('input[name="lastName"]').fill(self.profile["last_name"])
            form.locator('input[name="email"]').fill(self.email)
            if self.profile.get("phone"):
                form.locator('input[name="phone"]').fill(self.profile["phone"])

            # "Do you already own a property?" → No
            no_radio = form.locator('input[type="radio"][id^="sellingProperty-no"]')
            if no_radio.count():
                no_radio.first.check(force=True)

            visit = form.locator('input[type="checkbox"][id^="scheduleViewing"]')
            if visit.count():
                visit.first.check(force=True)

            alert = form.locator('input[type="checkbox"][id^="createAnAlert"]')
            if alert.count() and alert.first.is_checked():
                alert.first.uncheck(force=True)

            form.locator('textarea[name="message"]').fill(
                APPLICATION_MESSAGE.format(first_name=self.profile["first_name"])
            )

            # name="contact" is a hidden honeypot field — filling it marks you as a bot.
            honeypot = form.locator('input[name="contact"]')
            if honeypot.count() and honeypot.first.input_value():
                honeypot.first.fill("")
        except Exception as e:
            log(f"  Could not fill contact form: {e}. Screenshot: {self.screenshot(listing['id'] + '-fill')}")
            return False

        if not send:
            log(f"  [no-send] Form filled, NOT sent. Screenshot: {self.screenshot(listing['id'] + '-filled')}")
            return True

        submit = form.locator("button.sendMyRequestButton")
        try:
            with page.expect_response(
                lambda r: r.request.method == "POST" and "immoweb" in r.url, timeout=20000
            ) as resp_info:
                submit.click()
            resp = resp_info.value
        except PWTimeout:
            log(f"  No response after clicking Send. Screenshot: {self.screenshot(listing['id'] + '-nosend')}")
            return False

        page.wait_for_timeout(3000)
        shot = self.screenshot(listing["id"] + "-sent")
        errors = form.locator(".form__error, .input--error, [aria-invalid='true']")
        visible_errors = [e for e in errors.all() if e.is_visible()]
        if resp.status >= 400 or visible_errors:
            log(f"  Send failed (HTTP {resp.status}, {len(visible_errors)} form errors). Screenshot: {shot}")
            return False

        log(f"  Sent (HTTP {resp.status} from {resp.url}). Screenshot: {shot}")
        return True


# ─── CORE LOOP ────────────────────────────────────────────────────────────────


def log(msg: str) -> None:
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"[{ts}] {msg}", flush=True)


def format_listing(listing: dict) -> str:
    bedrooms = listing["bedrooms"]
    room_label = "Studio" if bedrooms == 0 else f"{bedrooms} BR"
    price = f"€{listing['price']}" if listing["price"] else "price unknown"
    charges = f" + €{listing['charges']} charges" if listing["charges"] else ""
    surface = f" | {listing['surface']}m²" if listing["surface"] else ""
    return (
        f"{room_label} in {listing['locality']} ({listing['postal_code']}) "
        f"| {price}{charges}{surface}"
    )


def run_check(session: ImmowebSession | None, state: dict, dry_run: bool, send: bool) -> None:
    log("─" * 60)
    log("Checking for new listings...")

    try:
        listings = fetch_listings()
    except RateLimited:
        raise
    except Exception as e:
        log(f"Search request failed: {e}")
        return

    skipped = state.setdefault("skipped", [])
    new_listings = [l for l in listings if l["id"] not in state["applied"] and l["id"] not in skipped]
    log(f"Found {len(listings)} total, {len(new_listings)} not applied/skipped yet.")

    applied_this_round = 0
    for listing in new_listings:
        lid = listing["id"]
        if lid not in state["seen"]:
            state["seen"].append(lid)
        log(f"NEW  {format_listing(listing)}")
        log(f"     {listing['url']}")

        try:
            avail = fetch_availability(listing)
        except RateLimited:
            save_state(state)
            raise
        except Exception as e:
            log(f"     Could not read availability ({e}); will retry next check.")
            continue
        avail_label = avail.isoformat() if isinstance(avail, date) else (avail or "not specified")
        if not availability_ok(avail):
            reason = "no date given" if avail is None else f"not {AVAILABLE_ON:%d %b %Y}"
            log(f"     Available: {avail_label} — {reason}, skipping.")
            skipped.append(lid)
            save_state(state)
            continue
        log(f"     Available: {avail_label} ✓")

        if dry_run or session is None:
            log("     [dry-run] Skipping apply.")
            continue

        if applied_this_round:
            time.sleep(DELAY_BETWEEN_APPLICATIONS_S)
        applied_this_round += 1
        log("     Applying...")
        if session.apply_to_listing(listing, send=send):
            if send:
                state["applied"].append(lid)
                log("     Applied ✓")
        elif lid not in state["failed"]:
            state["failed"].append(lid)
            log("     Apply failed ✗  (saved to failed list for manual review)")
        save_state(state)

    save_state(state)


def seconds_until_quiet_hours_end(now: datetime) -> float:
    """0 outside quiet hours, otherwise how long until they end. Handles ranges past midnight."""
    if not QUIET_HOURS:
        return 0
    start, end = QUIET_HOURS
    in_quiet = start <= now.hour < end if start < end else (now.hour >= start or now.hour < end)
    if not in_quiet:
        return 0
    resume = now.replace(hour=end, minute=0, second=0, microsecond=0)
    if resume <= now:
        resume += timedelta(days=1)
    return (resume - now).total_seconds()


def seed_state(state: dict) -> None:
    """First run: mark everything currently listed as seen, so we only apply to new ones."""
    listings = fetch_listings()
    state["seen"] = [l["id"] for l in listings]
    save_state(state)
    log(f"First run: recorded {len(listings)} existing listings as seen (not applying to them).")


# ─── ENTRY POINT ──────────────────────────────────────────────────────────────


def main():
    parser = argparse.ArgumentParser(description="Immoweb auto-monitor and apply")
    parser.add_argument("--headless", action="store_true",
                        help="Headless browser (usually blocked by Cloudflare)")
    parser.add_argument("--dry-run", action="store_true", help="Search only, no browser, no apply")
    parser.add_argument("--no-send", action="store_true", help="Fill the contact form but never send it")
    parser.add_argument("--apply-existing", action="store_true",
                        help="On first run, also apply to listings that already exist")
    parser.add_argument("--test-url", help="Run login + apply on this single listing URL, then exit")
    args = parser.parse_args()
    send = not args.no_send

    state = load_state()

    if args.dry_run:
        log("DRY RUN — search only.")
        try:
            run_check(None, state, dry_run=True, send=False)
        except RateLimited as e:
            log(f"Blocked by Immoweb ({e}). Try again later.")
        return

    email, password = ask_credentials()
    profile = load_profile()

    msg_len = len(APPLICATION_MESSAGE.format(first_name=profile["first_name"]))
    if msg_len > MESSAGE_MAX_LENGTH:
        log(f"APPLICATION_MESSAGE is {msg_len} chars; Immoweb allows {MESSAGE_MAX_LENGTH}. Shorten it.")
        sys.exit(1)

    log("=" * 60)
    log("Immoweb Monitor starting")
    log("Areas : Ixelles, Forest, Saint-Gilles, Etterbeek, Woluwe, Uccle")
    log(f"Budget: max €{MAX_PRICE}/month")
    log("Type  : Studio or 1 bedroom")
    log(f"Avail.: exactly {AVAILABLE_ON:%d %b %Y}"
        f"{'' if APPLY_IF_AVAILABILITY_UNKNOWN else ' (skip if not specified)'}")
    log(f"Poll  : every {POLL_INTERVAL_MINUTES[0]}–{POLL_INTERVAL_MINUTES[1]} min"
        + (f", paused {QUIET_HOURS[0]:02d}:00–{QUIET_HOURS[1]:02d}:00" if QUIET_HOURS else ""))
    log(f"Mode  : {'headless' if args.headless else 'visible Chrome'} | "
        f"{'live send' if send else 'NO-SEND (fill only)'}")
    log("=" * 60)

    with ImmowebSession(email, password, profile, headless=args.headless) as session:
        log("Logging in to Immoweb...")
        if not session.login():
            log("Login failed. Exiting.")
            sys.exit(1)
        log("Logged in successfully.")

        if args.test_url:
            lid = args.test_url.rstrip("/").split("/")[-1].split("?")[0]
            ok = session.apply_to_listing({"id": lid, "url": args.test_url}, send=send)
            log("Test result: " + ("OK" if ok else "FAILED"))
            return

        if not STATE_FILE.exists() and not args.apply_existing:
            seed_state(state)

        log("Press Ctrl+C to stop.")
        blocks_in_a_row = 0
        try:
            while True:
                wait_s = seconds_until_quiet_hours_end(datetime.now())
                if wait_s:
                    log(f"Quiet hours — sleeping until {QUIET_HOURS[1]:02d}:00.")
                    time.sleep(wait_s)
                    continue

                try:
                    run_check(session, state, dry_run=False, send=send)
                    blocks_in_a_row = 0
                    wait_s = random.uniform(*POLL_INTERVAL_MINUTES) * 60
                except RateLimited as e:
                    blocks_in_a_row += 1
                    backoff_min = min(BACKOFF_MINUTES * 2 ** (blocks_in_a_row - 1), MAX_BACKOFF_MINUTES)
                    wait_s = max(backoff_min * 60, e.retry_after_s or 0)
                    log(f"Blocked by Immoweb ({e}) — backing off {wait_s / 60:.0f} min.")

                log(f"Next check in {wait_s / 60:.1f} min.")
                time.sleep(wait_s)
        except KeyboardInterrupt:
            log("Stopped by user.")
            save_state(state)


if __name__ == "__main__":
    main()
