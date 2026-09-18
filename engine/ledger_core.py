"""LEDGER analytics — pure functions over transaction rows.

No I/O in here: server.py hands in lists of dicts (the mirror of Marcus's
spending.sqlite) and gets plain data back, so every rule below is unit-tested
against synthetic fixtures (test_ledger_core.py) and never against real money.

Row shape (Marcus's convention, kept as-is):
    uid, date 'YYYY-MM-DD', posted, amount (positive = money out), merchant,
    description, category, kind (Purchase / Payment / Credit / Interest / ...),
    card, ref, source ('statement' | 'shortcut' | 'manual'), imported_at

Python 3.9 syntax only — this runs under the Mac's /usr/bin/python3.
"""
import calendar
import re
import statistics
from datetime import date, datetime, timedelta

# cadence name -> (nominal days, tolerance in days)
CADENCES = (("weekly", 7, 2), ("biweekly", 14, 3), ("monthly", 30, 5),
            ("quarterly", 91, 10), ("yearly", 365, 15))
NEW_SERIES_DAYS = 62        # a series first seen this recently is NEW
PRICE_UP_RATIO = 1.03       # last charge this far over the earlier median = PRICE UP
DUPLICATE_DAYS = 2
DUPLICATE_MIN = 5.0
FIRST_TIME_MIN = 25.0
FIRST_TIME_HISTORY_DAYS = 60
FLAG_WINDOW_DAYS = 45       # only recent rows raise flags; history is the baseline
REFUND_MATCH_DAYS = 120

# Why a purchase happened. Spending is the fleet's clearest record of intent
# becoming action. The label is INFERRED from what was recorded around the moment
# (MOTIVE.md) - the owner is never asked. When he overrides one, that correction is
# stored here and is how the inference is scored. Deliberately few, and about the
# DECISION, not the category of goods.
INTENTS = (
    ("need", "Need", "had to - food, fuel, medicine, a bill"),
    ("routine", "Routine", "the usual, bought on autopilot"),
    ("planned", "Planned", "decided beforehand, then bought"),
    ("project", "Project", "gear or parts for something I am building"),
    ("treat", "Treat", "a reward or comfort, chosen knowingly"),
    ("impulse", "Impulse", "did not intend to until the moment"),
    ("social", "For someone", "a gift, a shared meal, someone else's need"),
)
INTENT_KEYS = tuple(k for k, _, _ in INTENTS)


# ------------------------------------------------------------------ basics
def d(s):
    """'YYYY-MM-DD' -> date."""
    return datetime.strptime(str(s)[:10], "%Y-%m-%d").date()


def klass(row):
    """purchase | refund | payment | interest | adjustment. Payments are card pay-downs, not
    refunds - Marcus's own summary lumps them together; LEDGER never does."""
    k = (row.get("kind") or "").strip().lower()
    if "payment" in k:
        return "payment"
    if "interest" in k:
        return "interest"
    # Apple Card "Debit" rows are Daily Cash Adjustments: the cashback clawed back
    # when a purchase is refunded. Card bookkeeping, not something the owner bought.
    if k == "debit" or "daily cash adjust" in ((row.get("merchant") or "") + " " + (row.get("description") or "")).lower():
        return "adjustment"
    return "refund" if (row.get("amount") or 0) < 0 else "purchase"


_PROCESSOR = re.compile(r"^(SQ|TST|PAYPAL|PP|SP|APLPAY)\s*\*\s*")     # the merchant comes AFTER the star
_STORE_NO = re.compile(r"(#\s*\d+|\b\d{3,}[A-Z]*\b)")                 # "#1482", "0987", "0194SAN"
_STREET = re.compile(r"\s+\d{1,6}\s+[A-Z].*$")                         # " 925 BLOSSOM HILL ROAD ..." to the end
_PUNCT = re.compile(r"[^A-Z0-9& ]+")


def merchant_key(name, aliases=None):
    """Stable grouping key: 'Safeway #1234' and 'SAFEWAY 0987' are one merchant.
    `aliases` maps a raw key to the key the owner chose for it."""
    s = (name or "").upper().strip()
    s = _PROCESSOR.sub("", s)          # "SQ *BLUE BOTTLE" is Blue Bottle, not Square
    if "*" in s:                       # "AMAZON MARK* B78F762A0410 TERRY AVE": the merchant is BEFORE the star,
        head = s.split("*", 1)[0].strip()      # and what follows is a per-order id that would split one
        if len(head) >= 3:                     # merchant into hundreds and hide every refund from its purchase
            s = re.sub(r"\s+[A-Z]$", "", head)  # "EBAY O*11-149.." -> "EBAY"
    s = _STORE_NO.sub(" ", s)
    s = _STREET.sub("", " " + s).strip()   # Apple's Merchant field sometimes drags the street address along
    s = _PUNCT.sub(" ", s)
    s = " ".join(s.split()) or "UNKNOWN"
    if aliases:
        s = aliases.get(s, s)
    return s


_ADDRESS = re.compile(r"\b(\d{5})\s+([A-Z]{2})\s+(USA?|US)\s*$")


def place_hint(description):
    """{'zip','state'} when the description ends the way Apple Card writes a US
    address ("... SPRINGFIELD 12345 XX USA"), else None. MOTIVE geocodes from this."""
    m = _ADDRESS.search((description or "").upper().strip())
    return {"zip": m.group(1), "state": m.group(2)} if m else None


# ------------------------------------------------------------- categories
# Apple files a third of the owner's purchases under "Other" (pharmacies, Amazon,
# Patreon, AI subscriptions, tobacco, tuition, car repair...). LEDGER keeps its
# own, finer set. Order of trust:
#   1. the owner's override on the row          4. the map's kind of place (OSM), but only
#   2. a NAME rule below                       when the name match was solid - a loose
#   3. Apple's category, when it is specific   match once called a storage unit a hairdresser
# Rules are regexes over "MERCHANT | DESCRIPTION", first hit wins, so specific
# brands sit above the general words that would also catch them.
NAME_RULES = (
    (r"\bDAILY CASH\b", "Card adjustments"),
    (r"\b(PATREON|KO-?FI|SUBSTACK|BUYMEACOFFEE)\b", "Creators & patronage"),
    (r"\b(CLAUDE|ANTHROPIC|OPENAI|CHATGPT|PANGRAM|MIDJOURNEY|GITHUB|CURSOR|JETBRAINS|MICROSOFT|ADOBE|1PASSWORD|TAILSCALE|DIGITALOCEAN|NAMECHEAP|CLOUDFLARE)\b", "Software & AI"),
    (r"\b(HBO|NETFLIX|HULU|DISNEY|PARAMOUNT|PEACOCK|SPOTIFY|YOUTUBE|AUDIBLE|KINDLE|APPLE SERVICES|APPLE COM BILL|AMAZON PRIME|PRIME VIDEO|CRUNCHYROLL|GOOGLE)\b", "Streaming & apps"),
    (r"\b(STEAM|PLAYSTATION|NINTENDO|XBOX|EPIC GAMES|OCULUS|META QUEST|GOG)\b", "Games"),
    (r"\b(POLLEN ROBOTICS|CULTS3D|BAMBU|PRUSA|ADAFRUIT|SPARKFUN|DIGIKEY|MOUSER|PRINTABLES|THINGIVERSE|MICRO CENTER)\b", "Maker & robotics"),
    (r"\b(GUITAR CENTER|REVERB|SWEETWATER|THOMANN|ABLETON|SPLICE|PLUGIN BOUTIQUE|NATIVE INSTRUMENTS|TORSO|ROLAND|AKAI)\b", "Music gear"),
    (r"\b(APPLE STORE|BEST BUY|LENOVO|NEWEGG|B&H|BHPHOTO|FRYS|SAMSUNG|DELL)\b", "Electronics"),
    (r"\b(AMAZON|AMZN|EBAY|ETSY|ALIEXPRESS|TEMU|WALMART COM|9TO5TOYS)\b", "Online shopping"),
    (r"\b(FHDA|DE ANZA|FOOTHILL|PARCHMENT|VISIBLEBODY|VISIBLE BODY|POCKET PREP|COURSERA|UDEMY|CHEGG|PEARSON|MCGRAW|CENGAGE|BOOKSTORE|CAMPUS STR|TUTORING)\b", "Education"),
    (r"\b(S?SMOKERS?|SMOKE SHOP|VAPE|TOBACCO|CIGAR|MONSTERS OF ROCK)\b", "Tobacco & vape"),
    (r"\b(KP NCAL|KAISER|DENTAL|DENTIST|ORTHODONT|OPTOMETR|MEDICAL|CLINIC|HOSPITAL|URGENT CARE|LABCORP|QUEST DIAG|PHYSICAL THERAPY)\b", "Health & dental"),
    (r"\b(WALGREENS|CVS|RITE AID|PHARMACY)\b", "Pharmacy"),
    (r"\b(USAA|GEICO|STATE FARM|PROGRESSIVE|ALLSTATE|INSURANCE)\b", "Insurance"),
    (r"\b(T-?MOBILE|VERIZON|AT&T|ATT\b|COMCAST|XFINITY|PG&E|PGE|SAN JOSE WATER|RECOLOGY|GARBAGE)\b", "Phone & utilities"),
    (r"\b(SELF STORAGE|PUBLIC STORAGE|EXTRA SPACE|U-?HAUL)\b", "Storage & moving"),
    (r"\b(AUTO REPAIR|AUTOZONE|O'?REILLY|PEP BOYS|JIFFY|SMOG|TIRE|FORTES BROTHERS|CAR WASH|DMV)\b", "Car care"),
    (r"\b(ARCO|CHEVRON|SHELL OIL|SHELL\b|VALERO|EXXON|MOBIL|\b76\b|COSTCO GAS|FUEL)\b", "Gas & fuel"),
    (r"\b(SERVICEWORKS|CSC SERVICE|LAUNDRY|LAUNDROMAT|DRY CLEAN)\b", "Laundry"),
    (r"\b(HOME DEPOT|LOWE'?S|ACE HARDWARE|OUTDOOR SUPPLY|HARDWARE|IKEA)\b", "Home & hardware"),
    (r"\b(COFFEE|COFFEESHOP|CAFE|ESPRESSO|STARBUCKS|PEET'?S|PHILZ|DUTCH BROS|7LEAVES|BOBA|TEA\b|TEAHOUSE)\b", "Coffee & tea"),
    (r"\b(MCDONALD|BURGER KING|WENDY|TACO BELL|JACK IN THE BOX|IN-?N-?OUT|CHICK-?FIL|POPEYES|KFC|SUBWAY|CHIPOTLE|PANDA EXPRESS|HABIT BURGER|FIVE GUYS|ANGRY CHICKZ|PAPA JOHN|DOMINO|LITTLE CAESARS|PIZZA HUT|WINGSTOP)\b", "Fast food"),
    (r"\b(TRADER JOE|SAFEWAY|GROCERY OUTLET|WHOLE FOODS|SPROUTS|LUCKY\b|COSTCO|SMART & FINAL|99 RANCH|H MART|MITSUWA|NIJIYA|7-?ELEVEN)\b", "Groceries"),
    (r"\b(MONTALVO|THEATRE|THEATER|CINEMA|AMC\b|CINEMARK|TICKETMASTER|EVENTBRITE|MUSEUM|CONCERT)\b", "Entertainment & arts"),
    (r"\b(H&M|UNIQLO|OLD NAVY|GAP\b|ZARA|NIKE|ADIDAS|ROSS\b|MARSHALLS|TJ ?MAXX|NORDSTROM|MACY)\b", "Clothing"),
    (r"\b(MICHAELS|JOANN|HOBBY LOBBY|BLICK)\b", "Hobby & craft"),
    (r"\b(TARGET|WALMART|DOLLAR TREE|DAISO|BIG LOTS)\b", "Shopping"),
    (r"\b(PLANET FITNESS|24 HOUR FIT|LA FITNESS|CRUNCH FIT|YMCA|GYM\b|CLIMBING|YOGA)\b", "Fitness"),
    (r"\b(UBER|LYFT|BART\b|VTA\b|CALTRAIN|CLIPPER|PARKING|FASTRAK|TOLL)\b", "Transport & parking"),
)
_NAME_RULES = tuple((re.compile(rx), cat) for rx, cat in NAME_RULES)
APPLE_CATEGORY = {"restaurants": "Restaurants", "grocery": "Groceries", "gas": "Gas & fuel", "utilities": "Phone & utilities",
                  "insurance": "Insurance", "medical": "Health & dental", "shopping": "Shopping",
                  "transportation": "Transport & parking", "tolls": "Transport & parking",
                  "govt-services-parking": "Government & fees", "hotels": "Travel", "airlines": "Travel",
                  "alcohol": "Alcohol", "entertainment": "Entertainment & arts", "payment": "Payment",
                  "interest": "Interest", "debit": "Card adjustments"}
OSM_CATEGORY = (("amenity:cafe", "Coffee & tea"), ("amenity:fast_food", "Fast food"), ("amenity:restaurant", "Restaurants"),
                ("amenity:bar", "Restaurants"), ("amenity:pub", "Restaurants"), ("amenity:ice_cream", "Restaurants"),
                ("shop:supermarket", "Groceries"), ("shop:convenience", "Groceries"), ("shop:bakery", "Groceries"),
                ("shop:greengrocer", "Groceries"), ("amenity:pharmacy", "Pharmacy"), ("shop:chemist", "Pharmacy"),
                ("shop:tobacco", "Tobacco & vape"), ("shop:e-cigarette", "Tobacco & vape"), ("amenity:fuel", "Gas & fuel"),
                ("shop:car_repair", "Car care"), ("shop:car_parts", "Car care"), ("shop:tyres", "Car care"),
                ("shop:electronics", "Electronics"), ("shop:computer", "Electronics"), ("shop:mobile_phone", "Phone & utilities"),
                ("shop:musical_instrument", "Music gear"), ("shop:hardware", "Home & hardware"),
                ("shop:doityourself", "Home & hardware"), ("shop:clothes", "Clothing"), ("shop:shoes", "Clothing"),
                ("shop:beauty", "Personal care"), ("shop:hairdresser", "Personal care"), ("shop:chocolate", "Treats & gifts"),
                ("shop:confectionery", "Treats & gifts"), ("shop:gift", "Treats & gifts"), ("amenity:theatre", "Entertainment & arts"),
                ("amenity:cinema", "Entertainment & arts"), ("amenity:arts_centre", "Entertainment & arts"),
                ("amenity:college", "Education"), ("amenity:university", "Education"), ("tourism:hotel", "Travel"),
                ("amenity:dentist", "Health & dental"), ("amenity:doctors", "Health & dental"), ("amenity:clinic", "Health & dental"),
                ("shop:art", "Hobby & craft"), ("shop:craft", "Hobby & craft"), ("shop:mall", "Shopping"),
                ("shop:department_store", "Shopping"), ("shop:alcohol", "Alcohol"), ("shop:pet", "Pets"))


def categorize(row, osm_kind=None):
    """LEDGER's category for a row, and which layer decided it: (category, 'name'|'apple'|'map'|'none').
    `osm_kind` must only be passed for a SOLID place match."""
    text = ("%s | %s" % (row.get("merchant") or "", row.get("description") or "")).upper()
    text = re.sub(r"[*#]", " ", text)
    for rx, cat in _NAME_RULES:
        if rx.search(text):
            return cat, "name"
    apple = (row.get("category") or "").strip().lower()
    mapped = APPLE_CATEGORY.get(apple)
    if mapped and mapped != "Restaurants":
        return mapped, "apple"
    if osm_kind:                       # Apple's "Restaurants" is coffee, fast food and sit-down in one bucket
        for k, cat in OSM_CATEGORY:
            if osm_kind.startswith(k):
                return cat, "map"
    if mapped:
        return mapped, "apple"
    return "Other", "none"


def prepare(rows, aliases=None, overrides=None, kinds=None):
    """Annotate rows once: _d (date), _k (klass), _m (merchant key), _cat, _cat_by.
    `kinds` = {merchant_key: OSM kind} for merchants whose place match is solid."""
    overrides = overrides or {}
    kinds = kinds or {}
    out = []
    for r in rows:
        r = dict(r)
        r["_d"] = d(r["date"])
        r["_k"] = klass(r)
        r["_m"] = merchant_key(r.get("merchant") or r.get("description"), aliases)
        if overrides.get(r.get("uid")):
            r["_cat"], r["_cat_by"] = overrides[r.get("uid")].strip(), "david"
        else:
            r["_cat"], r["_cat_by"] = categorize(r, kinds.get(r["_m"]))
        out.append(r)
    out.sort(key=lambda r: (r["_d"], r["_m"], r.get("uid") or ""))
    return out


def month_bounds(ym):
    y, m = int(ym[:4]), int(ym[5:7])
    return date(y, m, 1), date(y, m, calendar.monthrange(y, m)[1])


def prev_month(ym):
    y, m = int(ym[:4]), int(ym[5:7])
    return "%04d-%02d" % ((y, m - 1) if m > 1 else (y - 1, 12))


def _in(rows, since, until):
    return [r for r in rows if since <= r["_d"] <= until]


def totals(rows):
    spent = sum(r["amount"] for r in rows if r["_k"] == "purchase")
    refunded = -sum(r["amount"] for r in rows if r["_k"] == "refund")
    return {"spent": round(spent, 2), "refunded": round(refunded, 2),
            "net": round(spent - refunded, 2),
            "purchases": sum(1 for r in rows if r["_k"] == "purchase"),
            "payments": round(-sum(r["amount"] for r in rows if r["_k"] == "payment"), 2),
            "interest": round(sum(r["amount"] for r in rows if r["_k"] == "interest"), 2)}


# --------------------------------------------------------------- recurring
def _cadence(gaps):
    """The cadence most gaps agree on, or None. Needs 2/3 of gaps in tolerance."""
    if not gaps:
        return None
    med = statistics.median(gaps)
    for name, days, tol in CADENCES:
        if abs(med - days) <= tol:
            ok = sum(1 for g in gaps if abs(g - days) <= tol)
            if ok * 3 >= len(gaps) * 2:
                return name, days
    return None


def _thread(charges):
    """Split one merchant's date-sorted charges into price threads: a charge
    joins the thread whose last amount is nearest, if within 20 % and at least
    5 days later; otherwise it starts a new thread."""
    threads = []
    for r in charges:
        best = None
        for t in threads:
            last = t[-1]
            if (r["_d"] - last["_d"]).days < 5 or not last["amount"]:
                continue
            if abs(r["amount"] - last["amount"]) / last["amount"] <= 0.20:
                if best is None or abs(r["amount"] - last["amount"]) < abs(r["amount"] - best[-1]["amount"]):
                    best = t
        if best is None:
            threads.append([r])
        else:
            best.append(r)
    return threads


def _series(m, s, cad, today, confidence, variable):
    name, days = cad
    amounts = [r["amount"] for r in s]
    gaps = [(y["_d"] - x["_d"]).days for x, y in zip(s, s[1:])]
    last, first = s[-1], s[0]
    stopped = (today - last["_d"]).days > days * 1.5 + 3
    base = statistics.median(amounts[:-1])
    typical = statistics.median(amounts[-3:]) if variable else last["amount"]
    price_up = (not variable and len(s) >= 3 and last["amount"] > base * PRICE_UP_RATIO
                and last["amount"] - base >= 0.50)
    step = int(round(statistics.median(gaps)))
    return {
        # keyed on the first charge, so a price change or a longer history
        # never renames a series out from under 'reviewed' or a DOCKET ref
        "key": "%s|%s" % (m, first.get("uid")),
        "merchant": m, "display": last.get("merchant") or m, "category": last["_cat"],
        "cadence": name, "confidence": confidence, "variable": variable,
        "amount": round(typical, 2), "previous_amount": round(base, 2),
        "yearly": round(typical * 365.0 / days, 2),
        "charges": len(s), "first": first["date"], "last": last["date"],
        "next_expected": None if stopped else (last["_d"] + timedelta(days=step)).isoformat(),
        "status": "stopped" if stopped else "active",
        "new": (today - first["_d"]).days <= NEW_SERIES_DAYS and not stopped,
        "price_up": bool(price_up),
        "uids": [r.get("uid") for r in s],
    }


def recurring(rows, today):
    """Subscriptions and repeating bills. Two shapes are recognised:

    fixed price  - a thread of near-identical amounts on a steady cadence. One
                   merchant can carry several (Apple bills iCloud and Music
                   apart), and other purchases there do not disturb it. "Few
                   distinct amounts" is what stops a weekly grocery habit from
                   being cherry-picked into a fake monthly series.
    variable bill - a merchant charged about once a month or less and nothing
                   else (power, insurance): the whole merchant is the series."""
    by_m = {}
    for r in rows:
        if r["_k"] == "purchase":
            by_m.setdefault(r["_m"], []).append(r)
    out = []
    for m, charges in by_m.items():
        found = False
        for s in _thread(charges):
            n = len(s)
            if n < 2:
                continue
            distinct = len(set(round(r["amount"], 2) for r in s))
            if distinct > max(2, n // 3):
                continue
            cad = _cadence([(y["_d"] - x["_d"]).days for x, y in zip(s, s[1:])])
            if not cad:
                continue
            if n == 2 and (distinct != 1 or cad[0] != "monthly"):
                continue        # two charges are only believable to the cent
            # A subscription bills ONCE per period. A daily coffee at a fixed price threads
            # into several tidy "weekly" series (real data: one cafe, 267 charges, ten fake
            # subscriptions) - so if the merchant has other look-alike charges inside this
            # thread's span, it is a HABIT (see habits()), not a subscription.
            mid = statistics.median([r["amount"] for r in s])
            ids = set(id(r) for r in s)
            alike = sum(1 for r in charges if id(r) not in ids and s[0]["_d"] <= r["_d"] <= s[-1]["_d"]
                        and mid and abs(r["amount"] - mid) / mid <= 0.20)
            if alike * 2 >= n:
                continue
            out.append(_series(m, s, cad, today, "confirmed" if n >= 3 else "probable", False))
            found = True
        if not found and len(charges) >= 3:
            cad = _cadence([(y["_d"] - x["_d"]).days for x, y in zip(charges, charges[1:])])
            amounts = [r["amount"] for r in charges]
            mean = statistics.mean(amounts)
            if cad and cad[1] >= 30 and mean and statistics.pstdev(amounts) / mean < 0.5:
                out.append(_series(m, charges, cad, today, "confirmed", True))
    out.sort(key=lambda x: (x["status"] != "active", -x["yearly"]))
    return out


def habits(rows, today, days=90):
    """Places the owner buys from again and again - not billed to him, chosen by him.
    At least 8 purchases in the window, typically no more than 4 days apart.
    These are the clearest 'routine' purchases there are, and often the biggest
    line nobody thinks of as a bill."""
    since = today - timedelta(days=days)
    by_m = {}
    for r in rows:
        if r["_k"] == "purchase" and r["_d"] >= since:
            by_m.setdefault(r["_m"], []).append(r)
    span = max(1, min(days, (today - rows[0]["_d"]).days)) if rows else days
    out = []
    for m, rs in by_m.items():
        dates = sorted(set(r["_d"] for r in rs))
        if len(rs) < 8 or len(dates) < 6:
            continue
        gaps = [(b - a).days for a, b in zip(dates, dates[1:])]
        if statistics.median(gaps) > 4:
            continue
        total = sum(r["amount"] for r in rs)
        wd = [0] * 7
        for r in rs:
            wd[r["_d"].weekday()] += 1
        out.append({"merchant": m, "display": rs[-1].get("merchant") or m, "category": rs[-1]["_cat"],
                    "purchases": len(rs), "days_with_a_purchase": len(dates), "window_days": span,
                    "per_week": round(len(rs) * 7.0 / span, 1), "typical": round(statistics.median([r["amount"] for r in rs]), 2),
                    "total": round(total, 2), "yearly": round(total * 365.0 / span, 2),
                    "by_weekday": wd, "last": rs[-1]["date"]})
    out.sort(key=lambda h: -h["yearly"])
    return out


def upcoming(series, today, until):
    """Charges the recurring series predict between today and `until`."""
    out = []
    for s in series:
        if s["status"] != "active" or not s["next_expected"]:
            continue
        nxt = d(s["next_expected"])
        step = dict((n, dd) for n, dd, _ in CADENCES)[s["cadence"]]
        while nxt < today:                      # an overdue prediction rolls forward
            nxt += timedelta(days=step)
        while nxt <= until:
            out.append({"date": nxt.isoformat(), "merchant": s["display"], "amount": s["amount"],
                        "key": s["key"], "cadence": s["cadence"]})
            nxt += timedelta(days=step)
    out.sort(key=lambda x: x["date"])
    return out


# -------------------------------------------------------------------- pace
def pace(rows, today, series=None):
    """Month to date against the same day last month, and where the month lands.

    Projection = spent so far + recurring charges still due this month + the
    everyday run-rate for the days left. Early in a month the run-rate is mostly
    the trailing-90-day average; by month end it is the month's own."""
    ym = today.strftime("%Y-%m")
    start, end = month_bounds(ym)
    pstart, pend = month_bounds(prev_month(ym))
    mtd = totals(_in(rows, start, today))
    same_day = min(today.day, pend.day)
    last_mtd = totals(_in(rows, pstart, date(pstart.year, pstart.month, same_day)))
    last_full = totals(_in(rows, pstart, pend))

    series = series if series is not None else recurring(rows, today)
    rec_uids = set(u for s in series for u in s["uids"])
    due = upcoming(series, today + timedelta(days=1), end)
    due_total = sum(x["amount"] for x in due)

    days_in = end.day
    elapsed = today.day
    left = days_in - elapsed
    everyday_mtd = sum(r["amount"] for r in _in(rows, start, today)
                       if r["_k"] == "purchase" and r.get("uid") not in rec_uids)
    t90 = _in(rows, today - timedelta(days=90), today - timedelta(days=1))
    span = max(1, min(90, (today - rows[0]["_d"]).days)) if rows else 1
    everyday_90 = sum(r["amount"] for r in t90
                      if r["_k"] == "purchase" and r.get("uid") not in rec_uids) / float(span)
    w = elapsed / float(days_in)
    rate = w * (everyday_mtd / float(elapsed)) + (1 - w) * everyday_90
    projected = mtd["net"] + due_total + rate * left

    delta = None
    if last_mtd["net"] > 0:
        delta = round((mtd["net"] - last_mtd["net"]) / last_mtd["net"] * 100.0, 1)
    daily = []
    run = 0.0
    by_day = {}
    for r in _in(rows, start, today):
        if r["_k"] == "purchase":
            by_day[r["_d"].day] = by_day.get(r["_d"].day, 0.0) + r["amount"]
        elif r["_k"] == "refund":
            by_day[r["_d"].day] = by_day.get(r["_d"].day, 0.0) + r["amount"]
    for day in range(1, elapsed + 1):
        run += by_day.get(day, 0.0)
        daily.append(round(run, 2))
    pdaily, run = [], 0.0
    pby = {}
    for r in _in(rows, pstart, pend):
        if r["_k"] in ("purchase", "refund"):
            pby[r["_d"].day] = pby.get(r["_d"].day, 0.0) + r["amount"]
    for day in range(1, pend.day + 1):
        run += pby.get(day, 0.0)
        pdaily.append(round(run, 2))
    return {"month": ym, "day": elapsed, "days_in_month": days_in,
            "mtd": mtd, "last_month_same_day": last_mtd, "last_month_full": last_full,
            "delta_pct": delta, "projected": round(projected, 2),
            "recurring_still_due": round(due_total, 2), "due": due,
            "everyday_rate": round(rate, 2),
            "cumulative": daily, "last_month_cumulative": pdaily}


# ---------------------------------------------------- categories, merchants
def by_category(rows, since, until):
    cats = {}
    for r in _in(rows, since, until):
        if r["_k"] == "purchase":
            c = cats.setdefault(r["_cat"], {"category": r["_cat"], "spent": 0.0, "count": 0})
            c["spent"] += r["amount"]
            c["count"] += 1
        elif r["_k"] == "refund":
            c = cats.setdefault(r["_cat"], {"category": r["_cat"], "spent": 0.0, "count": 0})
            c["spent"] += r["amount"]
    out = [dict(c, spent=round(c["spent"], 2)) for c in cats.values()]
    out.sort(key=lambda c: -c["spent"])
    return out


def category_trend(rows):
    """{months: [...], series: [{category, values:[...]}]} net of refunds."""
    months, table = [], {}
    for r in rows:
        if r["_k"] not in ("purchase", "refund"):
            continue
        ym = r["date"][:7]
        if ym not in months:
            months.append(ym)
        table.setdefault(r["_cat"], {})
        table[r["_cat"]][ym] = table[r["_cat"]].get(ym, 0.0) + r["amount"]
    months.sort()
    series = [{"category": c, "values": [round(v.get(m, 0.0), 2) for m in months],
               "total": round(sum(v.values()), 2)} for c, v in table.items()]
    series.sort(key=lambda s: -s["total"])
    return {"months": months, "series": series}


def merchants(rows, since, until):
    ms = {}
    for r in _in(rows, since, until):
        if r["_k"] != "purchase":
            continue
        m = ms.setdefault(r["_m"], {"merchant": r["_m"], "display": r.get("merchant") or r["_m"],
                                     "category": r["_cat"], "spent": 0.0, "visits": 0, "last": r["date"]})
        m["spent"] += r["amount"]
        m["visits"] += 1
        m["last"] = max(m["last"], r["date"])
        m["display"] = r.get("merchant") or m["display"]
    out = []
    for m in ms.values():
        m["spent"] = round(m["spent"], 2)
        m["average"] = round(m["spent"] / m["visits"], 2)
        out.append(m)
    out.sort(key=lambda m: -m["spent"])
    return out


# ------------------------------------------------------------------- flags
def flags(rows, today, series=None, reviewed=None):
    """Things worth a second look, newest first. Every flag has a stable `id` so
    'reviewed' sticks across re-imports and DOCKET never re-proposes it."""
    reviewed = reviewed or set()
    series = series if series is not None else recurring(rows, today)
    rec_uids = set(u for s in series for u in s["uids"])
    purchases = [r for r in rows if r["_k"] == "purchase"]
    window = today - timedelta(days=FLAG_WINDOW_DAYS)
    out = []

    # duplicate: same merchant, same amount, within two days, not a subscription -
    # and not his USUAL ORDER. Real data: a $7.19 coffee most mornings raised 28
    # "double charges". A price he has paid there four or more times is a habit;
    # the same amount twice is only suspicious where it is unusual.
    usual = {}
    for r in purchases:
        k = (r["_m"], round(r["amount"], 2))
        usual[k] = usual.get(k, 0) + 1
    seen = {}
    for r in purchases:
        k = (r["_m"], round(r["amount"], 2))
        prev = seen.get(k)
        if (prev is not None and usual[k] < 4 and (r["_d"] - prev["_d"]).days <= DUPLICATE_DAYS
                and r["amount"] >= DUPLICATE_MIN and r["_d"] >= window
                and r.get("uid") not in rec_uids):
            out.append({"id": "dup:%s:%s" % (prev.get("uid"), r.get("uid")), "kind": "duplicate",
                        "date": r["date"], "merchant": r.get("merchant") or r["_m"],
                        "amount": round(r["amount"], 2), "uids": [prev.get("uid"), r.get("uid")],
                        "text": "Charged %.2f twice within %d day(s)" % (
                            r["amount"], (r["_d"] - prev["_d"]).days)})
        seen[k] = r

    # large: well above what this merchant usually costs, or above nearly everything
    by_m = {}
    for r in purchases:
        by_m.setdefault(r["_m"], []).append(r["amount"])
    recent_all = sorted(r["amount"] for r in purchases if r["_d"] >= today - timedelta(days=180))
    p98 = recent_all[int(len(recent_all) * 0.98) - 1] if len(recent_all) >= 50 else None
    for r in purchases:
        if r["_d"] < window:
            continue
        amts = by_m[r["_m"]]
        why = None
        if len(amts) >= 4:
            med = statistics.median(amts)
            if r["amount"] >= 50 and r["amount"] > 3 * med:
                why = "%.1fx the usual %.2f here" % (r["amount"] / med, med)
        if why is None and p98 is not None and r["amount"] >= 200 and r["amount"] >= p98:
            why = "among the largest charges in six months"
        if why:
            out.append({"id": "large:%s" % r.get("uid"), "kind": "large", "date": r["date"],
                        "merchant": r.get("merchant") or r["_m"], "amount": round(r["amount"], 2),
                        "uids": [r.get("uid")], "text": why})

    # first-time merchant, once there is enough history to call anything "first"
    if rows and (today - rows[0]["_d"]).days >= FIRST_TIME_HISTORY_DAYS:
        first = {}
        for r in purchases:
            first.setdefault(r["_m"], r)
        for m, r in first.items():
            if r["_d"] >= window and r["_d"] >= today - timedelta(days=30) and r["amount"] >= FIRST_TIME_MIN:
                out.append({"id": "first:%s" % r.get("uid"), "kind": "first-time", "date": r["date"],
                            "merchant": r.get("merchant") or m, "amount": round(r["amount"], 2),
                            "uids": [r.get("uid")], "text": "First purchase at this merchant"})

    # a large first-time purchase is ONE thing to look at, not two rows
    large = dict((f["uids"][0], f) for f in out if f["kind"] == "large")
    for f in [x for x in out if x["kind"] == "first-time" and x["uids"][0] in large]:
        large[f["uids"][0]]["text"] += "; first purchase at this merchant"
        out.remove(f)

    for f in out:
        f["reviewed"] = f["id"] in reviewed
    out.sort(key=lambda f: f["date"], reverse=True)      # newest first...
    out.sort(key=lambda f: f["reviewed"])                # ...unreviewed on top (stable)
    return out


# ----------------------------------------------------------------- refunds
def refunds(rows, today, awaiting=None):
    """Credits paired with the purchase they undo, and purchases the owner marked
    'awaiting refund' that no credit has answered yet.
    `awaiting` = {uid: 'YYYY-MM-DD' marked-on}."""
    awaiting = awaiting or {}
    purchases = [r for r in rows if r["_k"] == "purchase"]
    used, matched, unmatched = set(), [], []
    for c in [r for r in rows if r["_k"] == "refund"]:
        amt = -c["amount"]
        cands = [p for p in purchases
                 if p["_m"] == c["_m"] and p.get("uid") not in used and p["_d"] <= c["_d"]
                 and (c["_d"] - p["_d"]).days <= REFUND_MATCH_DAYS and p["amount"] + 0.005 >= amt]
        if cands:
            exact = [p for p in cands if abs(p["amount"] - amt) < 0.005]
            p = (exact or cands)[-1]
            used.add(p.get("uid"))
            matched.append({"refund_uid": c.get("uid"), "purchase_uid": p.get("uid"),
                            "merchant": c.get("merchant") or c["_m"], "refunded": round(amt, 2),
                            "purchase_amount": round(p["amount"], 2), "purchase_date": p["date"],
                            "refund_date": c["date"], "partial": amt + 0.005 < p["amount"]})
        else:
            unmatched.append({"refund_uid": c.get("uid"), "merchant": c.get("merchant") or c["_m"],
                              "refunded": round(amt, 2), "refund_date": c["date"]})
    pending = []
    by_uid = dict((p.get("uid"), p) for p in purchases)
    for uid, marked in awaiting.items():
        p = by_uid.get(uid)
        if p is None or uid in used:
            continue
        pending.append({"uid": uid, "merchant": p.get("merchant") or p["_m"],
                        "amount": round(p["amount"], 2), "purchase_date": p["date"],
                        "marked": marked, "waiting_days": (today - d(marked)).days})
    pending.sort(key=lambda x: -x["waiting_days"])
    matched.sort(key=lambda x: x["refund_date"], reverse=True)
    return {"pending": pending, "matched": matched, "unmatched": unmatched,
            "answered": sorted(u for u in awaiting if u in used)}


def intent_summary(rows, since, until, intents):
    """How the period's purchases split by the owner's stated reason.
    `intents` = {uid: intent key}. Untagged money is reported, never hidden."""
    out = dict((k, {"intent": k, "label": lab, "spent": 0.0, "count": 0}) for k, lab, _ in INTENTS)
    untagged = {"spent": 0.0, "count": 0}
    for r in _in(rows, since, until):
        if r["_k"] != "purchase":
            continue
        slot = out.get(intents.get(r.get("uid")), untagged)
        slot["spent"] += r["amount"]
        slot["count"] += 1
    tagged = [dict(v, spent=round(v["spent"], 2)) for v in out.values() if v["count"]]
    tagged.sort(key=lambda v: -v["spent"])
    n = sum(v["count"] for v in tagged) + untagged["count"]
    return {"by_intent": tagged, "untagged": {"spent": round(untagged["spent"], 2), "count": untagged["count"]},
            "coverage_pct": round(100.0 * (n - untagged["count"]) / n, 0) if n else None}


def interest_ytd(rows, year):
    items = [r for r in rows if r["_k"] == "interest" and r["_d"].year == year]
    return {"year": year, "total": round(sum(r["amount"] for r in items), 2),
            "months": [{"date": r["date"], "amount": round(r["amount"], 2)} for r in items]}


# ------------------------------------------------------------------ budgets
def budget_pace(rows, today, budgets):
    """budgets = {category: monthly target}. 'expected' is the straight-line
    share of the target for this day of the month."""
    ym = today.strftime("%Y-%m")
    start, end = month_bounds(ym)
    spent = dict((c["category"], c["spent"]) for c in by_category(rows, start, today))
    share = today.day / float(end.day)
    out = []
    for cat, target in sorted(budgets.items()):
        s = spent.get(cat, 0.0)
        out.append({"category": cat, "target": round(target, 2), "spent": round(s, 2),
                    "expected": round(target * share, 2),
                    "state": "over" if s > target else ("ahead" if s > target * share * 1.10 else "ok")})
    return out


# -------------------------------------------------------------- brief, status
def staleness(rows, today, last_push=None, last_import=None):
    last = rows[-1]["date"] if rows else None
    stale = (today - d(last)).days if last else None
    return {"rows": len(rows), "first": rows[0]["date"] if rows else None, "through": last,
            "stale_days": stale, "last_push": last_push, "last_import": last_import,
            "stale": stale is None or stale > 7}


def money(v):
    v = round(v, 2)
    return "$" + (format(int(v), ",d") if v == int(v) else format(v, ",.2f"))


def brief(rows, today):
    """One or two plain lines for Marcus's today block and DOCKET's morning text.
    Says how current it is whenever that matters - never silently under-reports."""
    if not rows:
        return "LEDGER: no transactions imported yet."
    st = staleness(rows, today)
    y = today - timedelta(days=1)
    ys = [r for r in rows if r["_d"] == y and r["_k"] == "purchase"]
    p = pace(rows, today)
    parts = []
    if st["stale"]:
        parts.append("data only through %s (%d days old) - export Apple Card to refresh" % (
            st["through"], st["stale_days"]))
    elif ys:
        parts.append("yesterday %s across %d purchase%s" % (
            money(sum(r["amount"] for r in ys)), len(ys), "" if len(ys) == 1 else "s"))
    line = "month to date %s" % money(p["mtd"]["net"])
    if p["delta_pct"] is not None:
        line += " (%+.0f%% vs this day last month)" % p["delta_pct"]
    line += ", on course for %s" % money(p["projected"])
    parts.append(line)
    return "LEDGER: " + "; ".join(parts) + "."


# ------------------------------------------------------------ cut spending
# Things the owner cannot simply decide to spend less on this month. They are never offered as levers.
# Bought by the basket, not by the visit: fewer trips buys the same food. These get a monthly-amount lever only.
BY_AMOUNT_ONLY = ("Groceries", "Gas & fuel")
NOT_A_LEVER = ("Health & dental", "Insurance", "Education", "Pharmacy", "Phone & utilities", "Car care",
               "Storage & moving", "Government & fees", "Card adjustments", "Payment", "Interest", "Laundry")


def levers(rows, today, series, habit_list, plan=None):
    """Where money could come from, in the owner's own numbers - three kinds of lever:

    habit         a place he chooses again and again: how many times a week?
    subscription  a repeating charge: keep or cancel
    category      everything ELSE in a category he can steer, as a monthly rate over the
                  last 90 days (one-offs left out), his own usual month beside it: what
                  monthly figure instead? Groceries and fuel live here, never as a habit.

    No dollar is offered twice: a category lever excludes purchases already covered by
    a habit or subscription lever. `plan` = {lever_id: chosen value}; each lever comes
    back with its saving per year under that choice, and habits with how the last 7
    days actually went against it."""
    plan = plan or {}
    out, covered = [], set()
    since30, since7 = today - timedelta(days=30), today - timedelta(days=7)
    purchases = [r for r in rows if r["_k"] == "purchase"]

    for h in habit_list:
        if h["category"] in NOT_A_LEVER or h["category"] in BY_AMOUNT_ONLY:
            continue
        mine = [r for r in purchases if r["_m"] == h["merchant"]]
        covered.update(r.get("uid") for r in mine)
        lid = "habit:" + h["merchant"]
        now = h["per_week"]
        chosen = plan.get(lid)
        last7 = sum(1 for r in mine if r["_d"] > since7)
        out.append({"id": lid, "kind": "habit", "title": h["display"], "category": h["category"],
                    "now": now, "typical": h["typical"], "yearly_now": h["yearly"],
                    "unit_yearly": round(h["typical"] * 52.0, 2), "min": 0, "max": math_ceil_half(now), "step": 0.5,
                    "chosen": chosen, "saving_yearly": round(max(0.0, now - chosen) * h["typical"] * 52.0, 2) if chosen is not None else 0.0,
                    "last7": last7, "on_plan": None if chosen is None else last7 <= chosen + 0.5})

    for s_ in series:
        if s_["status"] != "active" or s_["category"] in NOT_A_LEVER:
            continue
        covered.update(s_["uids"])
        lid = "sub:" + s_["key"]
        chosen = plan.get(lid)
        out.append({"id": lid, "kind": "subscription", "title": s_["display"], "category": s_["category"],
                    "amount": s_["amount"], "cadence": s_["cadence"], "yearly_now": s_["yearly"],
                    "next_expected": s_["next_expected"], "price_up": s_["price_up"], "new": s_["new"],
                    "chosen": chosen, "saving_yearly": s_["yearly"] if chosen == 0 else 0.0,
                    "still_charging": bool(chosen == 0 and s_["status"] == "active")})

    # categories: what is left after the levers above, as a monthly RATE over the last 90 days beside his
    # own usual month. One-offs are left out of both: a $640 laptop is not a rate, and annualising it once
    # produced "save $7,680 a year on electronics". A one-off = far above what that category usually costs.
    rest = [r for r in purchases if r.get("uid") not in covered and r["_cat"] not in NOT_A_LEVER]
    typical = {}
    for r in rest:
        typical.setdefault(r["_cat"], []).append(r["amount"])
    typical = dict((c, statistics.median(v)) for c, v in typical.items())
    rest = [r for r in rest if not (r["amount"] >= 200 and r["amount"] > 4 * typical[r["_cat"]])]
    this_month, since90 = today.strftime("%Y-%m"), today - timedelta(days=90)
    span = max(30, min(90, (today - rows[0]["_d"]).days)) if rows else 90
    months, recent, count = {}, {}, {}
    for r in rest:
        if r["date"][:7] != this_month:
            months.setdefault(r["_cat"], {})
            months[r["_cat"]][r["date"][:7]] = months[r["_cat"]].get(r["date"][:7], 0.0) + r["amount"]
        if r["_d"] > since90:
            recent[r["_cat"]] = recent.get(r["_cat"], 0.0) + r["amount"]
            count[r["_cat"]] = count.get(r["_cat"], 0) + 1
    full = sorted(set(r["date"][:7] for r in purchases if r["date"][:7] != this_month))
    for cat, total in sorted(recent.items(), key=lambda kv: -kv[1])[:8]:
        amt = total * 30.0 / span
        if amt < 20 or count[cat] < 3:
            continue
        hist = [months.get(cat, {}).get(m, 0.0) for m in full[-8:-3]] if len(full) >= 6 else []
        usual = statistics.median(hist) if len(hist) >= 3 else None
        lid = "cat:" + cat
        chosen = plan.get(lid)
        out.append({"id": lid, "kind": "category", "title": cat, "category": cat,
                    "now": round(amt, 2), "usual": None if usual is None else round(usual, 2), "purchases_90d": count[cat],
                    "above_usual": bool(usual and amt > usual * 1.15 and amt - usual >= 20),
                    "yearly_now": round(amt * 12.0, 2), "min": 0, "max": round(amt, 2), "step": 5,
                    "chosen": chosen, "saving_yearly": round(max(0.0, amt - chosen) * 12.0, 2) if chosen is not None else 0.0})

    # suggestions: the same levers, ranked by what they would give for the least pain
    ideas = []
    for l in out:
        if l["kind"] == "habit" and l["now"] >= 2:
            cut = max(1.0, round(l["now"] / 3.0 * 2) / 2.0)            # about a third fewer, in half-steps
            ideas.append({"lever": l["id"], "set": round(l["now"] - cut, 1), "saves_yearly": round(cut * l["unit_yearly"], 2),
                          "text": "%s: %g fewer a week (from %g to %g)" % (l["title"], cut, l["now"], round(l["now"] - cut, 1))})
        elif l["kind"] == "subscription" and (l["price_up"] or l["new"]):
            ideas.append({"lever": l["id"], "set": 0, "saves_yearly": l["yearly_now"],
                          "text": "%s: %s - still worth %s a year?" % (l["title"], "the price just went up" if l["price_up"] else "new this season", money(l["yearly_now"]))})
        elif l["kind"] == "category" and l["above_usual"]:
            ideas.append({"lever": l["id"], "set": l["usual"], "saves_yearly": round((l["now"] - l["usual"]) * 12.0, 2),
                          "text": "%s: back to your own usual month (%s instead of %s)" % (l["title"], money(l["usual"]), money(l["now"]))})
    ideas.sort(key=lambda i: -i["saves_yearly"])
    total = round(sum(l["saving_yearly"] for l in out), 2)
    return {"levers": out, "ideas": ideas[:6], "plan_saving_yearly": total, "plan_saving_monthly": round(total / 12.0, 2),
            "discretionary_yearly": round(sum(l["yearly_now"] for l in out), 2)}


def math_ceil_half(v):
    import math
    return math.ceil(v * 2.0) / 2.0


# --------------------------------------------------------- DOCKET candidates
def candidates(series, flag_list, refund_info, stale, cut=None):
    """What LEDGER would like on the owner's DOCKET. Every ref is stable, so a re-run
    never re-proposes; docket_sweep clears refs that stop appearing.
    Confidence is the routing: DOCKET auto-files telemetry at >= 0.85, so a FACT
    (data gone stale, a refund overdue) files itself, while a QUESTION (keep this
    subscription? is this a double charge?) waits in the tray at 0.8."""
    out = []
    for s in series:
        if s["status"] != "active":
            continue
        per = {"weekly": "wk", "biweekly": "2 wk", "monthly": "mo", "quarterly": "qtr", "yearly": "yr"}[s["cadence"]]
        if s["new"]:
            out.append({"ref": "ledger:new:%s" % s["key"], "kind": "task", "confidence": 0.8,
                        "title": "New subscription: %s %s/%s - keep it?" % (s["display"], money(s["amount"]), per),
                        "notes": "First charged %s, %d charge(s) so far, about %s a year." % (
                            s["first"], s["charges"], money(s["yearly"]))})
        if s["price_up"]:
            out.append({"ref": "ledger:priceup:%s:%s" % (s["key"], s["last"]), "kind": "task", "confidence": 0.8,
                        "title": "%s went up: %s -> %s" % (s["display"], money(s["previous_amount"]), money(s["amount"])),
                        "notes": "Charged %s. About %s a year at the new price." % (s["last"], money(s["yearly"]))})
    for f in flag_list:
        if f["kind"] == "duplicate" and not f["reviewed"]:
            out.append({"ref": "ledger:%s" % f["id"], "kind": "task", "confidence": 0.8,
                        "title": "Possible double charge: %s %s" % (f["merchant"], money(f["amount"])),
                        "notes": "%s (%s). Mark it reviewed in LEDGER if it is fine." % (f["text"], f["date"])})
    for r in refund_info["pending"]:
        if r["waiting_days"] > 14:
            out.append({"ref": "ledger:refund:%s" % r["uid"], "kind": "task", "confidence": 0.9,
                        "title": "Refund still missing: %s %s" % (r["merchant"], money(r["amount"])),
                        "notes": "Marked awaiting refund %s - %d days, no matching credit yet." % (
                            r["marked"], r["waiting_days"])})
    for l in (cut or {}).get("levers", []):
        if l["kind"] == "subscription" and l.get("still_charging"):     # HE decided this, in the cut-spending plan: a fact, so it files itself
            out.append({"ref": "ledger:cancel:%s" % l["id"], "kind": "task", "confidence": 0.9,
                        "title": "Cancel %s (your LEDGER plan) - saves %s a year" % (l["title"], money(l["yearly_now"])),
                        "notes": "You marked it to cancel in LEDGER's cut-spending plan. It still bills %s%s. "
                                 "This clears itself once the charges stop, or if you un-mark it." % (
                                     money(l["amount"]), (", next about %s" % l["next_expected"]) if l.get("next_expected") else "")})
    if stale["stale"] and stale["through"]:
        out.append({"ref": "ledger:stale:%s" % stale["through"], "kind": "task", "confidence": 0.95,
                    "title": "Export Apple Card to LEDGER (last 90 days)",
                    "notes": "Data stops at %s. Wallet > Apple Card > Card Balance > Statements > Export "
                             "Transactions > CSV > Save to Files > iCloud Drive > Spending. Imports itself." % stale["through"]})
    return out


# ------------------------------------------------ plain words, for Marcus
# Marcus's spending tools are dumb pipes to these: every rule and every phrasing
# lives here, so changing an answer never costs a restart of his 16k-line brain.
def _period(period, today):
    p = (period or "this_month").strip().lower().replace(" ", "_")
    if re.match(r"^\d{4}-\d{2}$", p):
        a, b = month_bounds(p)
        return a, min(b, today), a.strftime("%B %Y")
    if p in ("today",):
        return today, today, "today"
    if p in ("yesterday",):
        y = today - timedelta(days=1)
        return y, y, "yesterday"
    if p in ("week", "this_week", "last_7_days", "7d"):
        return today - timedelta(days=6), today, "the last 7 days"
    if p in ("last_month", "previous_month"):
        a, b = month_bounds(prev_month(today.strftime("%Y-%m")))
        return a, b, a.strftime("%B %Y")
    if p in ("year", "this_year", "ytd"):
        return date(today.year, 1, 1), today, "%d so far" % today.year
    a, _ = month_bounds(today.strftime("%Y-%m"))
    return a, today, today.strftime("%B %Y") + " so far"


def _caveat(rows, today):
    st = staleness(rows, today)
    if st["stale"]:
        return " CAVEAT: statement data stops at %s (%s days ago), so anything after that is missing - say so." % (
            st["through"], st["stale_days"])
    return " Data runs through %s." % st["through"]


def say_summary(rows, today, period=None, series=None):
    if not rows:
        return "LEDGER has no transactions yet - no Apple Card export has been imported."
    a, b, label = _period(period, today)
    sel = _in(rows, a, b)
    t = totals(sel)
    out = "%s: %s net across %d purchase%s" % (label[0].upper() + label[1:], money(t["net"]), t["purchases"],
                                               "" if t["purchases"] == 1 else "s")
    if t["refunded"]:
        out += " (%s spent, %s refunded)" % (money(t["spent"]), money(t["refunded"]))
    out += "."
    if label.endswith("so far") and a.day == 1 and a.month == today.month and a.year == today.year:
        p = pace(rows, today, series)
        if p["delta_pct"] is not None:
            out += " That is %+.0f%% against the same day last month (%s)." % (p["delta_pct"], money(p["last_month_same_day"]["net"]))
        out += " On course for about %s; last month finished at %s." % (money(p["projected"]), money(p["last_month_full"]["net"]))
    cats = [c for c in by_category(rows, a, b) if c["spent"] > 0][:4]
    if cats:
        out += " Biggest categories: " + ", ".join("%s %s" % (c["category"], money(c["spent"])) for c in cats) + "."
    ms = merchants(rows, a, b)[:4]
    if ms:
        out += " Biggest merchants: " + ", ".join("%s %s%s" % (m["display"], money(m["spent"]),
                                                  (" (%dx)" % m["visits"]) if m["visits"] > 1 else "") for m in ms) + "."
    if t["interest"]:
        out += " Interest charged: %s." % money(t["interest"])
    return out + _caveat(rows, today)


def say_search(rows, today, query, days=90, notes=None):
    if not rows:
        return "LEDGER has no transactions yet."
    q = (query or "").strip().lower()
    if not q:
        return "Say what to look for - a merchant, a category, or a word from a note."
    try:
        days = max(1, min(3650, int(days or 90)))
    except (TypeError, ValueError):
        days = 90
    notes = notes or {}
    since = today - timedelta(days=days)
    hits = [r for r in rows if r["_d"] >= since and q in " ".join(
        str(x or "") for x in (r.get("merchant"), r.get("description"), r["_cat"], notes.get(r.get("uid")))).lower()]
    if not hits:
        return "Nothing matching '%s' in the last %d days.%s" % (query, days, _caveat(rows, today))
    t = totals(hits)
    out = "'%s', last %d days: %d charge%s, %s spent" % (query, days, t["purchases"], "" if t["purchases"] == 1 else "s", money(t["spent"]))
    if t["refunded"]:
        out += ", %s refunded" % money(t["refunded"])
    out += ". Most recent: " + "; ".join("%s %s %s" % (r["_d"].strftime("%b %d").replace(" 0", " "), r.get("merchant") or r["_m"],
                                          money(r["amount"])) for r in list(reversed(hits))[:10]) + "."
    return out + _caveat(rows, today)


def _say_habits(habit_list):
    if not habit_list:
        return ""
    return " Habits (chosen, not billed): " + "; ".join("%s about %sx a week, typically %s, roughly %s a year" % (
        h["display"], ("%g" % h["per_week"]), money(h["typical"]), money(h["yearly"])) for h in habit_list[:5]) + "."


def say_recurring(series, rows, today, habit_list=None):
    active = [s for s in series if s["status"] == "active"]
    if not active:
        return "No subscriptions or repeating bills detected yet.%s%s" % (_say_habits(habit_list), _caveat(rows, today) if rows else "")
    per = {"weekly": "week", "biweekly": "2 weeks", "monthly": "month", "quarterly": "quarter", "yearly": "year"}
    yearly = sum(s["yearly"] for s in active)
    out = "%d repeating charges, about %s a year (%s a month): " % (len(active), money(yearly), money(yearly / 12.0))
    out += "; ".join("%s %s%s/%s%s%s, next %s" % (
        s["display"], "~" if s["variable"] else "", money(s["amount"]), per[s["cadence"]],
        " NEW" if s["new"] else "", (" PRICE UP from %s" % money(s["previous_amount"])) if s["price_up"] else "",
        d(s["next_expected"]).strftime("%b %d").replace(" 0", " ")) for s in active) + "."
    gone = [s for s in series if s["status"] == "stopped"]
    if gone:
        out += " Stopped: " + ", ".join("%s (last %s)" % (s["display"], s["last"]) for s in gone[:6]) + "."
    return out + _say_habits(habit_list) + _caveat(rows, today)


# ---------------------------------------------------- questions, answered in plain words
# "What if I stopped going out for coffee?"  "What am I most likely to buy at 3 pm on a Tuesday?"
# Marcus's model does the language; these do the arithmetic, so the figures he relays are exact.
SYNONYMS = {
    "coffee": ("Coffee & tea",), "cafe": ("Coffee & tea",), "cafes": ("Coffee & tea",), "tea": ("Coffee & tea",),
    "eating out": ("Restaurants", "Fast food"), "dining": ("Restaurants", "Fast food"), "restaurants": ("Restaurants", "Fast food"),
    "takeout": ("Restaurants", "Fast food"), "fast food": ("Fast food",), "food out": ("Restaurants", "Fast food", "Coffee & tea"),
    "going out": ("Restaurants", "Fast food", "Coffee & tea"), "groceries": ("Groceries",), "gas": ("Gas & fuel",),
    "fuel": ("Gas & fuel",), "smoking": ("Tobacco & vape",), "tobacco": ("Tobacco & vape",), "vaping": ("Tobacco & vape",),
    "cigarettes": ("Tobacco & vape",), "amazon": ("Online shopping",), "online shopping": ("Online shopping",),
    "ai": ("Software & AI",), "software": ("Software & AI",), "streaming": ("Streaming & apps",), "games": ("Games",),
    "gear": ("Music gear", "Electronics", "Maker & robotics"), "clothes": ("Clothing",), "patreon": ("Creators & patronage",),
}
WEEKDAYS = ("monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday")


def _select(rows, target):
    """Purchases a loose phrase refers to: a category, a synonym for one, or a merchant name. Longest phrase wins."""
    t = re.sub(r"[^a-z0-9& ]", " ", (target or "").lower()).strip()
    t = re.sub(r"\b(my|the|on|at|to|for|buying|going out for|going out to|spending|money|stuff|purchases)\b", " ", t)
    t = " ".join(t.split())
    purchases = [r for r in rows if r["_k"] == "purchase"]
    if not t:
        return [], None
    cats = set()
    for phrase in sorted(SYNONYMS, key=len, reverse=True):
        if re.search(r"\b%s\b" % re.escape(phrase), t):
            cats.update(SYNONYMS[phrase])
            break
    for c in set(r["_cat"] for r in purchases):
        if t in c.lower() or c.lower() in t:
            cats.add(c)
    if cats:
        return [r for r in purchases if r["_cat"] in cats], " + ".join(sorted(cats))
    hits = [r for r in purchases if t in (r.get("merchant") or "").lower() or t in r["_m"].lower()]
    return hits, (hits[-1].get("merchant") or t) if hits else None


def say_whatif(rows, today, series, target, change=None, days=90):
    if not rows:
        return "LEDGER has no transactions yet."
    t = (target or "").lower()
    if re.search(r"\bsubscri|\bsubs\b|recurring|repeating", t):
        active = [s for s in series if s["status"] == "active"]
        total = sum(s["yearly"] for s in active)
        return ("Subscriptions and repeating bills: %d active, %s a year (%s a month). Cancelling all of them saves that; one by one: %s.%s" % (
            len(active), money(total), money(total / 12.0),
            "; ".join("%s %s a year" % (s["display"], money(s["yearly"])) for s in active[:10]), _caveat(rows, today)))
    sel, label = _select(rows, target)
    if not sel:
        return "Nothing in LEDGER matches '%s'. Try a category (coffee, eating out, groceries, gas, amazon, tobacco) or a merchant name.%s" % (target, _caveat(rows, today))
    since = today - timedelta(days=days)
    recent = [r for r in sel if r["_d"] >= since]
    span = max(14, min(days, (today - rows[0]["_d"]).days))
    if not recent:
        last = sel[-1]
        return "%s: nothing in the last %d days (last was %s, %s). Nothing to save at the current rate.%s" % (label, days, last["date"], money(last["amount"]), _caveat(rows, today))
    total = sum(r["amount"] for r in recent)
    yearly, per_week = total * 365.0 / span, len(recent) * 7.0 / span
    typical = statistics.median([r["amount"] for r in recent])
    places = {}
    for r in recent:
        places[r.get("merchant") or r["_m"]] = places.get(r.get("merchant") or r["_m"], 0) + r["amount"]
    top = sorted(places.items(), key=lambda kv: -kv[1])
    out = "%s: %d purchases in the last %d days - about %.1f a week, typically %s - which runs %s a month, %s a year." % (
        label, len(recent), span, per_week, money(typical), money(yearly / 12.0), money(yearly))
    out += " Mostly %s." % ", ".join("%s (%s)" % (n, money(v)) for n, v in top[:3])
    ch, frac, how = (change or "stop").lower(), 1.0, "Stopping entirely"
    m = re.search(r"(\d+(?:\.\d+)?)\s*%", ch)
    w = re.search(r"(\d+(?:\.\d+)?)\s*(?:x|times)?\s*(?:a|per|/)\s*week", ch)
    if m:
        frac, how = min(1.0, float(m.group(1)) / 100.0), "Cutting it by %s%%" % m.group(1)
    elif w and per_week > 0:
        keep = float(w.group(1))
        frac, how = max(0.0, (per_week - keep) / per_week), "Going down to %g a week" % keep
    elif re.search(r"half|halve|50", ch):
        frac, how = 0.5, "Halving it"
    out += " %s would save about %s a year (%s a month)." % (how, money(yearly * frac), money(yearly * frac / 12.0))
    if frac == 1.0:
        out += " Halving it: %s a year. One fewer a week: %s a year." % (money(yearly / 2.0), money(typical * 52.0))
    return out + " Based on the last %d days, not a forecast.%s" % (span, _caveat(rows, today))


def say_pattern(rows, today, timed, weekday=None, hour=None):
    """What he tends to buy on a weekday and/or around an hour. The statement has DATES for every purchase
    but TIMES for only some (`timed` = [{ts, merchant, category, amount}]), and the answer says which is which."""
    if not rows:
        return "LEDGER has no transactions yet."
    purchases = [r for r in rows if r["_k"] == "purchase"]
    wd = None
    for i, name in enumerate(WEEKDAYS):
        if weekday and (name.startswith(str(weekday).lower()[:3])):
            wd = i
    try:
        hr = int(float(hour)) % 24 if hour not in (None, "") else None
    except (TypeError, ValueError):
        m = re.search(r"(\d{1,2})\s*(am|pm)?", str(hour).lower())
        hr = None if not m else (int(m.group(1)) % 12 + (12 if m.group(2) == "pm" else 0)) % 24
    out = []
    if wd is not None:
        sel = [r for r in purchases if r["_d"].weekday() == wd]
        days_all = set()
        dd = purchases[0]["_d"]
        while dd <= today:
            if dd.weekday() == wd:
                days_all.add(dd)
            dd += timedelta(days=1)
        active = set(r["_d"] for r in sel)
        cats, ms = {}, {}
        for r in sel:
            cats[r["_cat"]] = cats.get(r["_cat"], 0) + 1
            ms[r.get("merchant") or r["_m"]] = ms.get(r.get("merchant") or r["_m"], 0) + 1
        name = WEEKDAYS[wd].capitalize()
        if sel:
            out.append("%ss (%d of them on record): you buy something on %d%%, about %.1f purchases and %s on a day you do. Most likely: %s. Places: %s." % (
                name, len(days_all), round(100.0 * len(active) / max(1, len(days_all))), len(sel) / float(max(1, len(active))),
                money(sum(r["amount"] for r in sel) / float(max(1, len(active)))),
                ", ".join("%s (%d%% of %s purchases)" % (c, round(100.0 * n / len(sel)), name) for c, n in sorted(cats.items(), key=lambda kv: -kv[1])[:4]),
                ", ".join("%s x%d" % (m_, n) for m_, n in sorted(ms.items(), key=lambda kv: -kv[1])[:4])))
        else:
            out.append("No purchases on any %s on record." % name)
    if hr is not None:
        near = [t for t in timed if abs(((datetime.fromtimestamp(t["ts"]).hour - hr + 12) % 24) - 12) <= 1]
        same = [t for t in near if wd is None or datetime.fromtimestamp(t["ts"]).weekday() == wd]
        label = "%d %s" % (hr % 12 or 12, "am" if hr < 12 else "pm")
        pick = same if len(same) >= 4 else near
        scope = ("on %ss" % WEEKDAYS[wd].capitalize()) if (wd is not None and pick is same) else "on any day"
        if pick:
            ms = {}
            for t in pick:
                ms[t["merchant"]] = ms.get(t["merchant"], 0) + 1
            out.append("Around %s %s: %d purchases with a known time - %s, typically %s." % (
                label, scope, len(pick), ", ".join("%s x%d" % (m_, n) for m_, n in sorted(ms.items(), key=lambda kv: -kv[1])[:5]),
                money(statistics.median([t["amount"] for t in pick]))))
        else:
            out.append("Around %s: no purchase with a known time." % label)
        out.append("CAVEAT: the statement carries dates, not times - the time of day is known for only %d of %d purchases (stops Mapblock recorded, receipt emails), so by-hour answers are thin and lean recent; by-weekday answers cover everything." % (len(timed), len(purchases)))
    if not out:
        return "Say a weekday, an hour, or both - e.g. weekday='tuesday', hour=15."
    return " ".join(out) + _caveat(rows, today)


# -------------------------------------------------------------- notifications
# the owner, 09-17: "notifications on the phone that would help me be more aware of my spending and help
# me cut down". Few, specific, in his own numbers, never nagging. Every nudge has a stable id so it is
# sent once; the sender (ledger_nudge.py) adds the manners: quiet hours, never while driving, two a day.
NUDGE_KINDS = (
    ("charge", "A bill is about to hit", "the day before a subscription you marked Cancel, or a pricey one, bills"),
    ("overplan", "Over your own plan", "when a habit passes the weekly number you chose in Cut spending"),
    ("target", "A category target is nearly spent", "at 80% and at 100% of a monthly target you set"),
    ("flag", "A charge worth a second look", "a probable double charge, or one far above what that place usually costs"),
    ("pace", "The month is running hot", "once a month, if it is heading well past your usual - one-offs left out"),
    ("weekly", "Sunday evening recap", "the week in four lines: spent, vs usual, your plan, next week's bills"),
    ("checkin", "Did I get that right?", "minutes after a Wallet tap: what LEDGER thinks you just bought and why - reply y, n, or what it was. Only when it is unsure enough to be worth asking; at most three a day"),
)
NUDGE_KEYS = tuple(k for k, _, _ in NUDGE_KINDS)


def nudges(rows, now, series, cut, budgets, flag_list, stale):
    """Everything worth saying right now -> [{id, kind, text}]. Pure: no clock but `now`, no sending.
    Nothing is said on stale data - a nudge about "this week" built on a ten-day-old export would be a lie."""
    today = now.date()
    out = []
    if not rows or stale.get("stale"):
        return out
    fresh = stale.get("stale_days") is not None and stale["stale_days"] <= 2

    tomorrow = today + timedelta(days=1)
    chosen = dict((l["id"], l) for l in (cut or {}).get("levers", []))
    for s_ in series:
        if s_["status"] != "active" or not s_["next_expected"] or d(s_["next_expected"]) not in (today, tomorrow):
            continue
        lever = chosen.get("sub:" + s_["key"], {})
        when = "today" if d(s_["next_expected"]) == today else "tomorrow"
        if lever.get("chosen") == 0:
            text = "%s bills about %s (%s) - and you marked it to cancel. %s a year if it stays." % (s_["display"], when, money(s_["amount"]), money(s_["yearly"]))
        elif s_["price_up"]:
            text = "%s bills about %s at its NEW price, %s (was %s)." % (s_["display"], when, money(s_["amount"]), money(s_["previous_amount"]))
        elif s_["yearly"] >= 250:
            text = "%s bills about %s: %s (%s a year)." % (s_["display"], when, money(s_["amount"]), money(s_["yearly"]))
        else:
            continue
        out.append({"id": "charge:%s:%s" % (s_["key"], s_["next_expected"]), "kind": "charge", "text": text})

    week = "%d-W%02d" % today.isocalendar()[:2]
    if fresh:
        for l in (cut or {}).get("levers", []):
            if l["kind"] == "habit" and l.get("chosen") is not None and l["last7"] > l["chosen"] + 0.5:
                out.append({"id": "overplan:%s:%s" % (l["id"], week), "kind": "overplan",
                            "text": "%s: %d in the last 7 days - your plan is %g. Each is about %s; the plan is worth %s a year." % (
                                l["title"], l["last7"], l["chosen"], money(l["typical"]), money(l["saving_yearly"]))})

    for b in budgets or []:
        pct = b["spent"] / b["target"] if b["target"] else 0
        for mark in (100, 80):
            if pct * 100 >= mark:
                left = (month_bounds(today.strftime("%Y-%m"))[1] - today).days
                fmt = "%s: past your %s target (%s so far) with %d days left." if mark == 100 else \
                      "%s: 80%% of your %s target is spent (%s) with %d days left."
                out.append({"id": "target:%s:%s:%d" % (b["category"], today.strftime("%Y-%m"), mark), "kind": "target",
                            "text": fmt % (b["category"], money(b["target"]), money(b["spent"]), left)})
                break

    for f in flag_list:
        if not f["reviewed"] and f["kind"] in ("duplicate", "large") and (today - d(f["date"])).days <= 7:
            if f["kind"] == "duplicate":
                text = "Charged twice? %s %s on %s. Mark it fine in LEDGER if it is." % (f["merchant"], money(f["amount"]), f["date"][5:])
            else:
                text = "%s %s on %s - %s." % (f["merchant"], money(f["amount"]), f["date"][5:], f["text"])
            out.append({"id": "flag:" + f["id"], "kind": "flag", "text": text})

    if today.day >= 10:
        lv = [l for l in (cut or {}).get("levers", [])]
        monthly_now = sum(l["yearly_now"] for l in lv) / 12.0
        usual = sum((l.get("usual") if l["kind"] == "category" and l.get("usual") else l["yearly_now"] / 12.0) for l in lv)
        if usual > 0 and monthly_now > usual * 1.25 and monthly_now - usual >= 100:
            out.append({"id": "pace:" + today.strftime("%Y-%m"), "kind": "pace",
                        "text": "The spending you decide is running about %s a month lately against a usual %s (bills and one-offs left out). Cut spending in LEDGER shows where." % (
                            money(monthly_now), money(usual))})

    if now.weekday() == 6 and 17 <= now.hour < 21 and fresh:
        a = today - timedelta(days=6)
        wk = [r for r in rows if a <= r["_d"] <= today and r["_k"] == "purchase" and r["_cat"] not in NOT_A_LEVER]
        prior = [r for r in rows if a - timedelta(days=56) <= r["_d"] < a and r["_k"] == "purchase" and r["_cat"] not in NOT_A_LEVER]
        usual_wk = sum(r["amount"] for r in prior) / 8.0
        spent = sum(r["amount"] for r in wk)
        lines = ["This week: %s across %d purchases (your usual week is %s)." % (money(spent), len(wk), money(usual_wk))]
        big = sorted(wk, key=lambda r: -r["amount"])[:2]
        if big:
            lines.append("Biggest: " + ", ".join("%s %s" % (r.get("merchant") or r["_m"], money(r["amount"])) for r in big) + ".")
        planned = [l for l in (cut or {}).get("levers", []) if l["kind"] == "habit" and l.get("chosen") is not None]
        if planned:
            lines.append("Plan: " + "; ".join("%s %d of %g%s" % (l["title"], l["last7"], l["chosen"], "" if l["on_plan"] else " (over)") for l in planned) + ".")
        due = upcoming(series, tomorrow, today + timedelta(days=7))
        if due:
            lines.append("Billing next week: " + ", ".join("%s %s" % (x["merchant"], money(x["amount"])) for x in due[:5]) + ".")
        out.append({"id": "weekly:" + week, "kind": "weekly", "text": " ".join(lines)})
    return out


# ------------------------------------------------------- build instead of buy
# the owner, 09-17: "suggestions on areas I am spending that could be alleviated by writing code to fulfil
# the need demonstrated by the spending". He has done it before (TubeBlock for YouTube Premium, Beam for
# AirDrop). LEDGER only lists what he pays for software, services and subscriptions; whether code could
# meet the need is a judgement, made by Marcus - who knows the fleet - not by a rule in here.
BUILDABLE = ("Software & AI", "Streaming & apps", "Games", "Creators & patronage")
BUILDABLE_NAMES = re.compile(r"\b(VISIBLE ?BODY|POCKET PREP|PANGRAM|CULTS3D|PRINTABLES|ICLOUD|DROPBOX|EVERNOTE|NOTION|1PASSWORD|VPN)\b")
NEVER_BUILDABLE = ("Insurance", "Phone & utilities", "Health & dental", "Groceries", "Gas & fuel", "Pharmacy")


def buildable(rows, today, series):
    since = today - timedelta(days=365)
    billed = dict((u, s_) for s_ in series for u in s_["uids"])
    by = {}
    for r in rows:
        if r["_k"] != "purchase" or r["_d"] < since or r["_cat"] in NEVER_BUILDABLE:
            continue
        text = ("%s %s" % (r.get("merchant") or "", r.get("description") or "")).upper()
        if not (r["_cat"] in BUILDABLE or r.get("uid") in billed or BUILDABLE_NAMES.search(text)):
            continue
        b = by.setdefault(r["_m"], {"merchant": r.get("merchant") or r["_m"], "category": r["_cat"], "spent": 0.0, "charges": 0,
                                    "last": r["date"], "cadence": None, "active": False})
        b["spent"] += r["amount"]
        b["charges"] += 1
        b["last"] = max(b["last"], r["date"])
        s_ = billed.get(r.get("uid"))
        if s_:
            b["cadence"], b["active"] = s_["cadence"], b["active"] or s_["status"] == "active"
    span = max(30, min(365, (today - rows[0]["_d"]).days)) if rows else 365
    out = []
    for b in by.values():
        b["spent"] = round(b["spent"], 2)
        b["yearly"] = round(b["spent"] * 365.0 / span, 2)
        out.append(b)
    out.sort(key=lambda b: -b["yearly"])
    return out


def buildable_prompt(items):
    lines = ["%s - %s a year (%s, %d charge%s, last %s%s)" % (
        b["merchant"], money(b["yearly"]), b["category"], b["charges"], "" if b["charges"] == 1 else "s", b["last"],
        ", bills every %s" % b["cadence"].replace("ly", "") if b["cadence"] else "") for b in items[:18]]
    return ("the owner writes his own software and runs his own fleet - you know what he has already built. Below is what he "
            "pays per year for software, services and subscriptions, from LEDGER (exact figures - use only these, invent none). "
            "For EACH line give: the need it serves; whether code he writes could meet that need - YES, PARTLY or NO - and how, "
            "naming pieces of his fleet it could build on; a rough effort (an evening / a weekend / weeks); and what he would "
            "lose by leaving. Be blunt: most things are NOT worth replacing, and a model subscription is not replaced by a "
            "weekend of code. End with the two or three that would actually pay off, and the yearly total they add up to.\n\n"
            + "\n".join(lines))
