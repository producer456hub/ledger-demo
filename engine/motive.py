#!/usr/bin/python3
"""MOTIVE, part one - WHERE and WHEN each purchase happened.

The Apple Card export has a date, a merchant name and an address tail; no time,
no coordinates. This module recovers both from what the fleet already records
(design: MOTIVE.md), and says how it knows:

  merchant_at  where the store is. The offline geocoder (polaris-server/geo.py,
               380k named California places) resolves NAMES, not street
               addresses, so a merchant is looked up by name - biased at the
               place the owner actually stopped that day when there is one, which
               also settles "which Trader Joe's".
  moment       when. A purchase at a merchant within 250 m of one of that day's
               stops happened during that stop. Stops come from Mapblock's visit
               detector (5 min floor) plus gaps in the GPS track where he did not
               move (a 3-minute coffee pickup).
  channel      in_person | online | billed. Online and billed purchases are never
               pinned to a warehouse or a head office.

Every row carries `time_source` and `geo_source`; nothing pretends to precision
it lacks, and rows that cannot be placed say so rather than vanish.

Pure functions up top (unit-tested with invented coordinates); the I/O at the
bottom reads polaris.db READ-ONLY and imports geo.py from its own repo. Python 3.9.
"""
import json
import math
import os
import re
import sqlite3
import sys
from datetime import datetime, timedelta
from pathlib import Path

import ledger_core as lc

HERE = Path(__file__).resolve().parent
DB = Path(os.environ.get("LEDGER_DB") or (HERE / "ledger.db"))
POLARIS = Path(os.environ.get("POLARIS_DIR") or (Path.home() / "polaris-server"))

STOP_MATCH_KM = 0.25        # a merchant this close to a stop IS that stop (plaza parking lots are wide)
GAP_STOP_SECONDS = 180      # the GPS track standing still this long is a stop...
GAP_STOP_KM = 0.12          # ...if the next fix is still here (a far next fix is a recording gap, not a stop)
LOCAL_KM = 120              # a name that only resolves farther than this from the owner's range is the wrong branch
# billed from an office, bought from a couch: a street address on these says nothing about where he was
ONLINE = ("AMAZON", "APPLE SERVICES", "APPLE COM", "PATREON", "GOOGLE", "OPENAI", "CLAUDE AI", "ANTHROPIC",
          "HBO MAX", "NETFLIX", "SPOTIFY", "EBAY", "PAYPAL", "ETSY", "UBER", "LYFT", "DOORDASH", "GITHUB",
          "MICROSOFT", "ADOBE", "STEAM", "PLAYSTATION", "NINTENDO", "AUDIBLE", "KINDLE", "DISNEY", "HULU")
# A web order says so in its statement line: a domain, "WEB ORDER", "BIGBOXCOM8069...", or a phone number where an
# in-person line has the town ("... 888BIGBOXX 12345 XX USA", "... 800-555-0100 12345 XX USA"). Real data 2026-09-18:
# two web orders billed from another state were pinned beside the shop he visits most.
PHONE_FOR_TOWN = re.compile(r"(?:\b\d{3}-\d{3}-\d{3,4}|\b\d{3}-\d{7}|\b\d{10}|\b8(?:00|33|44|55|66|77|88)[A-Z]{7})\s+\d{5}(?:-\d{4})?\s*[A-Z]{2}\s+USA?\s*$")
ONLINE_MARK = re.compile(r"\.(?:COM|NET|US|ORG|IO|AI)\b|\bWWW\b|\bWEB ?ORDER\b|^[A-Z]+COM\d|" + PHONE_FOR_TOWN.pattern)
ZIP_TAIL = re.compile(r"((?:[A-Z][A-Z.'-]*\s+){0,2}[A-Z][A-Z.'-]*)\s*(\d{5})(?:-\d{4})?\s*[A-Z]{2}\s+(?:USA?|US)\s*$")     # "... TOWN 12345 XX USA"
STAYS = ("Travel",)         # a hotel prints its reservations line where the town goes, and he slept there all the same
# pay on the way out; everything else (counters, pumps), on the way in
CHECKOUT_LAST = ("Groceries", "Shopping", "Pharmacy", "Home & hardware", "Electronics", "Clothing", "Hobby & craft",
                 "Music gear", "Alcohol", "Treats & gifts", "Health & dental", "Car care")


def km(a, b):
    la1, lo1, la2, lo2 = map(math.radians, (a[0], a[1], b[0], b[1]))
    h = math.sin((la2 - la1) / 2) ** 2 + math.cos(la1) * math.cos(la2) * math.sin((lo2 - lo1) / 2) ** 2
    return 6371.0 * 2 * math.asin(math.sqrt(h))


def name_variants(merchant):
    """'7leaves Cafe - Cam' -> ['7leaves Cafe - Cam', '7leaves Cafe', '7leaves'].
    Apple truncates names and appends branch hints; the index knows the brand."""
    s = re.sub(r"[*#].*$", "", merchant or "")
    s = re.sub(r"\s+\d.*$", "", s).strip()
    out = [s] if s else []
    head = s.split(" - ")[0].strip()
    if head and head not in out:
        out.append(head)
    words = head.split()
    while len(words) > 1:
        words = words[:-1]
        v = " ".join(words)
        if len(v) >= 5 and v not in out:
            out.append(v)
    return out[:4]


def channel(row, hint, billed):
    """in_person | online | billed."""
    if billed:
        return "billed"
    key = row["_m"]
    if any(key.startswith(o) or (" " + o + " ") in (" " + key + " ") for o in ONLINE):
        return "online"
    if not hint:
        return "online"             # no address tail at all: a web checkout
    line = re.sub(r"\s*\((?:RETURN|REVERSAL)\)\s*$", "", (row.get("description") or "").upper().strip())
    if ONLINE_MARK.search(line.replace("GOSQ.COM", " ")):          # Square prints its own domain where the town goes, on a counter sale too
        if not (row.get("_cat") in STAYS and PHONE_FOR_TOWN.search(line) and not ONLINE_MARK.search(PHONE_FOR_TOWN.sub("", line))):
            return "online"
    return "in_person"


def stops_from_fixes(fixes):
    """[(ts, lat, lon)] sorted by ts -> stops where the track stood still.
    The track is deduped at 25 m, so standing still writes NOTHING: a stop is a
    long gap between two fixes that are still in the same place."""
    out = []
    for a, b in zip(fixes, fixes[1:]):
        if b[0] - a[0] >= GAP_STOP_SECONDS and km(a[1:], b[1:]) <= GAP_STOP_KM:
            out.append({"arrive": a[0], "depart": b[0], "lat": a[1], "lon": a[2], "place": None, "src": "gps-gap"})
    return out


def merge_stops(visits, gaps):
    """Detector visits win; a GPS-gap stop is kept only where no visit covers it."""
    out = list(visits)
    for g in gaps:
        if not any(v["arrive"] - 60 <= g["arrive"] <= (v["depart"] or v["arrive"]) + 60 for v in visits):
            out.append(g)
    out.sort(key=lambda s: s["arrive"])
    return out


def pay_time(stop, category):
    """A point estimate inside the stop: checkout-last trades pay near the end,
    counters and pumps near the start. The window is what is known; this is a guess
    and is stored as one."""
    a, d = stop["arrive"], stop["depart"] or stop["arrive"] + 600
    if category in CHECKOUT_LAST:
        return max(a, d - 240)
    return min(d, a + 240)


def match_day(purchases, stops, geocode):
    """Pair one day's in-person purchases with that day's stops.
    geocode(name, (lat, lon)) -> {'lat','lon','name'} | None.  Returns {uid: {...}}."""
    out, cache = {}, {}
    for p in purchases:
        best = None
        for s in stops:
            for v in name_variants(p.get("merchant") or p["_m"]):
                k = (v, round(s["lat"], 3), round(s["lon"], 3))
                if k not in cache:
                    cache[k] = geocode(v, (s["lat"], s["lon"]))
                g = cache[k]
                if not g:
                    continue
                d = km((g["lat"], g["lon"]), (s["lat"], s["lon"]))
                if d <= STOP_MATCH_KM and (best is None or d < best[0]):
                    best = (d, s, g, v)
                if g:
                    break               # the fullest name that resolves is the one to trust
        if best:
            d, s, g, v = best
            out[p["uid"]] = {"ts": pay_time(s, p["_cat"]), "ts_lo": s["arrive"], "ts_hi": s["depart"] or s["arrive"],
                             "time_source": "visit" if s["src"] == "visit" else "gps-gap",
                             "merchant_lat": g["lat"], "merchant_lon": g["lon"], "merchant_place": g["name"],
                             "geo_source": "stop-match", "david_lat": s["lat"], "david_lon": s["lon"],
                             "david_place": s.get("place"), "evidence": {"stop_km": round(d, 3), "matched_as": v}}
    return out


# ------------------------------------------------------------------ which branch
# The index answers a NAME with the match nearest the bias point, and the bias is the statement's town: every
# branch of a chain in his city landed on the one nearest downtown (real data 2026-09-18: 14 chains, 2-3 ZIPs each on
# one pin; a shop in his own plaza drawn 5.6 km away). The statement also names the STREET, and the index
# holds that street's bus stops ("River Expressway & Elm Lane") - points along it. The branch on that street
# is the branch; places already pinned in the same ZIP by a real stop referee a mistyped street ("RIVRE EXPY").
SAME_PLACE_KM = 0.3         # index entries this close together are one place mapped twice (a node and its building)
STREET_KM = 0.8             # a branch this close to a stop on the statement's street is the one on that street
ZIP_KM = 5.0                # a branch farther than this from everything stop-matched in its ZIP is another ZIP's
_STREET_WORD = {"EXPY": "expressway", "AVE": "avenue", "AV": "avenue", "BLVD": "boulevard", "BVD": "boulevard", "RD": "road",
                "LN": "lane", "ST": "street", "DR": "drive", "HWY": "highway", "PKWY": "parkway", "PKY": "parkway", "CT": "court",
                "PL": "place", "CIR": "circle", "TER": "terrace", "SQ": "square"}
_COMPASS = frozenset("N S E W NE NW SE SW".split())
_TAIL = re.compile(r"\s*\d{5}(?:-\d{4})?\s*[A-Z]{2}\s+(?:USA?|US)\s*$")


def street_of(description, town):
    """'CORNER MART 14290 1421 ELM LN SPRINGFIELD 12345 XX USA', 'Springfield' -> ['elm', 'lane'] - the words to look
    the street up by, abbreviations spelled out, a truncated last word left as the prefix it is. None if unreadable."""
    head = _TAIL.sub("", re.sub(r"\s*\((?:RETURN|REVERSAL)\)\s*$", "", (description or "").upper().strip()))
    t = (town or "").upper().strip()
    if not t or not head.endswith(t):
        return None
    # the leftmost number a street follows ("14290 1421 ELM LN": the first is the store's); a suite may trail it
    m = re.search(r"\S*\d\S*\s+((?:[A-Z][A-Z.'&-]*\s?)+?)\s*(?:,.*|#.*|(?<=\s)(?:STE|SUITE|BLDG|UNIT|FLOOR)\b.*)?$", head[:-len(t)].strip())
    if not m:
        return None
    words = [w.strip(".'") for w in m.group(1).split()]
    words = [w for w in words if w and w not in _COMPASS]
    if not words or (len(words) == 1 and words[0] in _STREET_WORD):
        return None
    return [_STREET_WORD.get(w, w).lower() if i else w.lower() for i, w in enumerate(words)]


def pick_branch(cands, anchors, zip_anchor=None):
    """cands [(lat, lon, label)] - every branch of the name in the statement's town; anchors [(lat, lon)] - points on
    the statement's street; zip_anchor - the middle of what is already stop-matched in that ZIP. -> the branch;
    None when there is one place to choose from (the ordinary lookup stands); False when there are several and
    nothing says which - the town, marked approximate, is honest and the branch nearest downtown is a coin toss."""
    if len(cands) < 2 or all(km(c[:2], cands[0][:2]) <= SAME_PLACE_KM for c in cands):
        return None
    pool = cands
    if zip_anchor:
        pool = [c for c in cands if km(c[:2], zip_anchor) <= ZIP_KM] or cands
    if anchors:
        off = lambda c: min(km(c[:2], a) for a in anchors)
        best = min(pool, key=off)
        if off(best) <= STREET_KM:
            return best
    if zip_anchor and len(pool) < len(cands):
        return min(pool, key=lambda c: km(c[:2], zip_anchor))
    return False


# words any place might carry: they say nothing about WHICH place the index found
GENERIC = frozenset("and the of by at restaurant bar grill cafe store shop market company inc llc "
                    "hardware pharmacy supermarket".split())
# the index holds these, but nobody pays at a bus stop or a post box
NOT_A_SHOP = ("public_transport:", "highway:", "railway:", "place:", "natural:", "building:", "amenity:post_box",
              "amenity:bench", "amenity:parking", "leisure:park", "leisure:dog_park", "leisure:playground")


def solid(merchant, resolved, town=None):
    """Did the index really find THIS merchant? Every telling word of the found name must be in the
    merchant's own (a found word may run on past the merchant's last one: Apple truncates, "Brewing Com"),
    or the found name must start with the whole merchant ("Baskin" -> Baskin-Robbins). Matching the
    leading word alone put an auto repair shop at "Metro City Restaurant" and a dentist at a dry cleaner sharing its first word.
    `town` (the statement's): a found name whose telling words are ONLY that town names another business there - a cafe
    named after its town, missing from the index, took a boutique named after the same town (09-18)."""
    words = lambda x: re.sub(r"[^a-z0-9]+", " ", (x or "").lower().replace("'", "").replace("’", "")).split()
    m = words(re.sub(r"[*#].*$", "", merchant or ""))
    r = words((resolved or "").split(",")[0])              # "Chevron, Springfield": the town is the index's, not the name
    if not m or not r:
        return False
    mc, rc = "".join(m), "".join(r)
    if len(mc) >= 6 and rc.startswith(mc):
        return True
    telling = [w for w in r if len(w) >= 3 and w not in GENERIC]
    if town and telling and set(telling) <= set(words(town)):
        return False
    return (bool(telling) and m[0] in rc
            and all(w in mc or (len(m[-1]) >= 3 and w.startswith(m[-1])) for w in telling))


# ------------------------------------------------------------------ tap pairing
def pair_taps(taps, purchases, day_stops, geocode):
    """Wallet taps -> the statement rows they were. A tap is the purchase MOMENT, exact to the
    second; the automation's payload is often empty (docket #107), so pairing leans on, in order:
      amount    the tap carried one, and exactly one of that day's purchases matches it
      place     the owner was at a stop when it fired, and one of that day's merchants is there
      only-one  one tap and one unpaired in-person purchase that day
    Taps a few seconds apart are one purchase (the automation can fire twice). Statement rows
    arrive days after the tap, so unpaired taps are normal and are returned, not dropped."""
    out, used, left = {}, set(), []
    # One purchase fires the automation more than once: the first real Watch tap (2026-09-17) arrived at
    # 15:03:44, 15:04:44 and 15:04:44. Keep the FIRST of any run of taps within 150 s of the last one kept.
    kept = []
    for t in sorted(taps, key=lambda t: t["epoch"]):
        if not kept or t["epoch"] - kept[-1]["epoch"] > 150:
            kept.append(t)
    taps = kept
    by_day = {}
    for p in purchases:
        by_day.setdefault(p["date"], []).append(p)
    day_taps = {}
    for t in taps:
        day_taps.setdefault(datetime.fromtimestamp(t["epoch"]).strftime("%Y-%m-%d"), []).append(t)
    for day, ts in day_taps.items():
        cands = by_day.get(day, [])
        for t in ts:
            free = [p for p in cands if p["uid"] not in used]
            hit, grade, extra = None, None, {}
            try:
                amt = float(re.sub(r"[^0-9.]", "", str(t.get("amount") or "")) or "nan")
            except ValueError:
                amt = float("nan")
            same = [p for p in free if abs(p["amount"] - amt) < 0.005]
            if len(same) == 1:
                hit, grade = same[0], "amount"
            told = [p for p in free if t.get("said_mkey") and p["_m"] == t["said_mkey"]]
            if hit is None and told:                  # he answered the check-in: that is the merchant, no inference needed
                hit, grade = told[0], "he said so"
            if hit is None and geocode:
                stop = next((s for s in day_stops.get(day, []) if s["arrive"] - 180 <= t["epoch"] <= (s["depart"] or s["arrive"]) + 180), None)
                if stop:
                    best = None
                    for p in free:
                        for v in name_variants(p.get("merchant") or p["_m"]):
                            g = geocode(v, (stop["lat"], stop["lon"]))
                            if g:
                                dkm = km((g["lat"], g["lon"]), (stop["lat"], stop["lon"]))
                                if dkm <= STOP_MATCH_KM and (best is None or dkm < best[0]):
                                    best = (dkm, p, g)
                                break
                    if best:
                        hit, grade = best[1], "place"
                        extra = {"merchant_lat": best[2]["lat"], "merchant_lon": best[2]["lon"], "merchant_place": best[2]["name"],
                                 "geo_source": "stop-match", "david_lat": stop["lat"], "david_lon": stop["lon"], "david_place": stop.get("place")}
            if hit is None and len(free) == 1 and len(ts) == 1:
                hit, grade = free[0], "only-one"
            if hit is None:
                left.append(t)
                continue
            used.add(hit["uid"])
            out[hit["uid"]] = dict(extra, ts=t["epoch"], ts_lo=t["epoch"], ts_hi=t["epoch"], time_source="tap",
                                   evidence={"tap": grade, "tap_id": t.get("id")})
    return out, left


# --------------------------------------------------------------------- intent
# Inferred, never asked (MOTIVE.md s4). Rules first, because a rule can be read and argued
# with: every call carries the evidence that produced it. enrich.intent is the owner's correction
# of a wrong call, and is how these rules get scored.
STAPLE = ("Groceries", "Gas & fuel", "Pharmacy", "Phone & utilities", "Insurance", "Health & dental", "Education",
          "Car care", "Laundry", "Storage & moving", "Government & fees", "Transport & parking")
PROJECT = ("Maker & robotics", "Music gear", "Electronics", "Software & AI", "Home & hardware", "Hobby & craft")
PLEASURE = ("Coffee & tea", "Restaurants", "Fast food", "Treats & gifts", "Entertainment & arts", "Alcohol", "Games",
            "Tobacco & vape", "Streaming & apps")
SHARED = ("Restaurants", "Fast food", "Coffee & tea", "Treats & gifts", "Entertainment & arts")


def infer_intent(f):
    """f = facts about one purchase (any may be missing - a missing fact is never evidence):
      category, amount, channel ('in_person'|'online'|'billed'), habit (bool), merchant_count,
      first_time (bool), usual_amount (bool), typical (merchant median), hour, weekday,
      trail_h (hours before the buy the merchant was last mentioned in messages / to Marcus),
      trail_from_other (bool), promo_h (marketing mail from this merchant), content_h (a post,
      caption or video naming it), feed_min_60, msgs_60, people_60, short_sleep (bool),
      high_stress (bool), worked_out (bool), tasks_done (int)
    -> {intent, confidence, prompted_by, evidence: [str]}"""
    cat, amount = f.get("category") or "Other", f.get("amount") or 0.0
    score = dict((k, 0.0) for k in lc.INTENT_KEYS)
    why = dict((k, []) for k in lc.INTENT_KEYS)

    def add(intent, pts, text):
        score[intent] += pts
        why[intent].append(text)

    if f.get("channel") == "billed":
        return {"intent": "routine", "confidence": 0.95, "prompted_by": "a repeating charge",
                "evidence": ["part of a subscription or repeating bill - nobody decided anything that day"]}
    staple, n = cat in STAPLE, f.get("merchant_count") or 0
    if staple:
        add("need", 2.0, "%s is something you have to buy" % cat.lower())
        if f.get("usual_amount"):
            add("need", 1.0, "about what it usually costs there")
        if f.get("habit") or n >= 8:
            add("need", 1.0, "your regular place for it (%d purchases)" % n)
    else:
        if f.get("habit"):
            add("routine", 2.5, "a habit: you buy here again and again (%d purchases)" % n)
            if f.get("usual_amount"):
                add("routine", 1.0, "your usual order, near %s" % lc.money(f.get("typical") or amount))
            if f.get("usual_hour"):
                add("routine", 1.0, "at your usual hour for it")
        elif n >= 8 and (f.get("usual_amount") or not f.get("typical") or amount <= 2 * f["typical"]):
            # not frequent enough to be a HABIT (that needs several a week), but a regular all the same:
            # real data called a smoke shop with 20-odd purchases a "treat"
            add("routine", 2.0, "a regular of yours (%d purchases)" % n)
            if f.get("usual_amount"):
                add("routine", 1.0, "about what you usually spend there, near %s" % lc.money(f.get("typical") or amount))
        if cat in PROJECT:
            add("project", 1.5, "%s is what you build things with" % cat.lower())
            if amount >= 100:
                add("project", 0.5, "a considered amount, not pocket change")
        if cat in PLEASURE and not f.get("habit") and n < 8:
            add("treat", 1.5, "%s, and not one of your habits" % cat.lower())
            if f.get("worked_out"):
                add("treat", 0.5, "on a day you worked out")
            if (f.get("tasks_done") or 0) >= 2:
                add("treat", 0.5, "after clearing %d tasks" % f["tasks_done"])
    if f.get("trail_h") is not None and f["trail_h"] >= 2:
        days_ = f["trail_h"] / 24.0
        add("planned", 2.5, "it came up %s before you bought it" % ("%d days" % round(days_) if days_ >= 1.5 else "%d hours" % round(f["trail_h"])))
        if amount >= 100:
            add("planned", 0.5, "and it was not a small amount")
    if not staple and f.get("channel") != "billed":
        if f.get("first_time"):
            add("impulse", 1.5, "first time you ever bought from them")
        elif 0 < n <= 2:
            add("impulse", 0.75, "a place you almost never buy from")
        if f.get("channel") == "online" and cat not in PROJECT and n < 8:      # online is only a tell where he does not shop all the time
            add("impulse", 0.75, "bought online")
        if f.get("hour") is not None and (f["hour"] >= 21 or f["hour"] < 5):
            add("impulse", 1.0, "late, around %d:00" % f["hour"])
        if (f.get("feed_min_60") or 0) >= 15:
            add("impulse", 1.0, "after %d minutes in feeds in the hour before" % round(f["feed_min_60"]))
        if f.get("content_h") is not None and f["content_h"] <= 72:
            add("impulse", 1.5, "a post or video named them %d hours earlier" % round(f["content_h"]))
        if f.get("promo_h") is not None and f["promo_h"] <= 48:
            add("impulse", 1.5, "their marketing email arrived %d hours earlier" % round(f["promo_h"]))
        if f.get("short_sleep"):
            add("impulse", 0.5, "on short sleep")
        if f.get("high_stress"):
            add("impulse", 0.5, "on a high-stress day")
        if f.get("trail_h") is not None and f["trail_h"] >= 2:
            score["impulse"] = max(0.0, score["impulse"] - 1.5)       # something talked about days ahead is not an impulse
    if cat in SHARED:
        if (f.get("msgs_60") or 0) >= 10 and (f.get("people_60") or 0) >= 1:
            add("social", 1.5, "%d messages with %d %s around that hour" % (f["msgs_60"], f["people_60"], "person" if f["people_60"] == 1 else "people"))
        if f.get("typical") and amount >= 2 * f["typical"] and amount >= 25:
            add("social", 1.0, "about twice what you spend there alone")
    if cat == "Treats & gifts":
        add("social", 1.0, "a gift shop")

    ranked = sorted(score.items(), key=lambda kv: -kv[1])
    top, second = ranked[0], ranked[1]
    if top[1] <= 0:
        return {"intent": None, "confidence": 0.0, "prompted_by": "unknown", "evidence": ["nothing on record points anywhere"]}
    conf = top[1] / (top[1] + second[1] + 1.0)
    if len(why[top[0]]) <= 1:
        conf = min(conf, 0.55)
    prompted = "unknown"
    if f.get("promo_h") is not None and f["promo_h"] <= 48:
        prompted = "a marketing email"
    elif f.get("content_h") is not None and f["content_h"] <= 72:
        prompted = "a post or video"
    elif f.get("trail_h") is not None and f["trail_h"] <= 24 and f.get("trail_from_other"):
        prompted = "a person"
    elif f.get("context_known"):
        prompted = "nothing seen"
    return {"intent": top[0], "confidence": round(max(0.3, min(0.95, conf)), 2), "prompted_by": prompted,
            "evidence": why[top[0]], "runner_up": second[0] if second[1] > 0 else None}


# ------------------------------------------------------------ the check-in guess
# A tap says WHEN, to the second, and nothing else (the payload is empty). Before the statement arrives days
# later, what was it? Three sources, strongest first:
#   here    a GPS fix fresh enough to trust, within 300 m of a merchant he has bought from before
#   hour    what he has bought around this hour before (only purchases whose time is known can vote)
#   habit   what he buys most, lately, on this weekday
# The result is a probability, and the check-in only speaks in the middle band: sure enough to be worth
# confirming, not so sure that asking is a waste of his attention.
ASK_BAND = (0.35, 0.90)
FRESH_FIX_S = 900


AREA_KM = 3.0                # "in that area": the home town is about this wide
AREA_FADES_S = 4 * 3600      # a last-seen position says less and less, and nothing after four hours


def guess_purchase(purchases, timed, habit_keys, when, here=None, merchant_geo=None, approx=None):
    """purchases = prepared rows; timed = [{ts, mkey}]; when = datetime of the tap;
    here = (lat, lon, age_seconds) | None; merchant_geo = {mkey: (lat, lon)} or {mkey: [(lat, lon, approx), ...]} -
    a chain has a pin per branch, and standing in ANY of them is standing in that merchant (one pin per key meant
    the branch in the last ZIP, so a fresh fix inside his own grocery store matched nothing);
    approx = mkeys whose position is only the TOWN's (not in the index): near means "in that town".
    -> {merchant, mkey, category, p, basis, runner_up} | None"""
    from datetime import timedelta
    score, basis = {}, {}

    def add(k, pts, why):
        score[k] = score.get(k, 0.0) + pts
        basis.setdefault(k, [])
        if why not in basis[k]:
            basis[k].append(why)

    approx = approx or set()
    spots = dict((k, [(p[0], p[1], bool(p[2]) if len(p) > 2 else k in approx) for p in (v if isinstance(v, list) else [v])])
                 for k, v in (merchant_geo or {}).items())
    within = lambda k, limit, rough: any(a == rough and km((here[0], here[1]), (la, lo)) <= limit for la, lo, a in spots[k])
    for r in purchases:          # everywhere he has ever bought can be the answer; lately counts for more
        lately = r["_d"] >= when.date() - timedelta(days=60)
        add(r["_m"], (0.05 if lately else 0.015) * (1.6 if r["_d"].weekday() == when.weekday() else 1.0),
            "one of your regular places lately" if lately else "you have bought there before")
    for t in timed:
        th = datetime.fromtimestamp(t["ts"])
        dh = abs(((th.hour + th.minute / 60.0) - (when.hour + when.minute / 60.0) + 12) % 24 - 12)
        if dh <= 2:
            add(t["mkey"], (1.0 if dh <= 1 else 0.5) * (1.5 if th.weekday() == when.weekday() else 1.0), "you have bought there around this hour before")
    if here and here[2] <= FRESH_FIX_S and merchant_geo:
        near = [k for k in spots if within(k, 0.3, False)]
        if not near:        # nobody he knows is at this exact spot - but a merchant known only by its town may well be
            near = [k for k in spots if within(k, AREA_KM, True)]
        if near:
            # Standing in the shop is not one more vote, it is the answer: eleven past coffees at this hour
            # once outvoted a fresh fix inside the grocery store. Everywhere he is NOT falls away.
            for k in list(score):
                if k not in near:
                    score[k] *= 0.05
            for k in near:
                add(k, 6.0, "your phone was right there")
                basis[k].remove("your phone was right there")
                basis[k].insert(0, "your phone was right there")
    elif here and here[2] <= AREA_FADES_S and merchant_geo:
        # No fresh fix - but he was LAST SEEN somewhere, and that is a clue, not nothing. First real check-in
        # (2026-09-17): last fix 67 min old at lunch in the home town; the purchase was a cafe in the home town; the guess,
        # having thrown the position away as stale, said a cafe in San Jose.
        # Mapblock records his drives, so NO newer fix also means he has not driven anywhere since: the longer
        # the silence, the less that holds, but for the first hour or two it is nearly decisive.
        w = 1.0 - here[2] / float(AREA_FADES_S)
        mins = int(here[2] // 60)
        for k in list(score):
            if k in spots and (within(k, AREA_KM, False) or within(k, AREA_KM, True)):
                score[k] *= 1.0 + 8.0 * w
                basis[k].insert(0, "you were last seen in that area %d min earlier, and have not driven since" % mins)
            else:
                score[k] *= 0.02 ** w          # 67 min of silence: x0.06. Four hours: x1 - it says nothing any more.
    if not score:
        return None
    total = sum(score.values())
    ranked = sorted(score.items(), key=lambda kv: -kv[1])
    k, top = ranked[0]
    rows = [r for r in purchases if r["_m"] == k]
    cats = {}
    for r in rows:
        cats[r["_cat"]] = cats.get(r["_cat"], 0) + 1
    amounts = sorted(r["amount"] for r in rows)
    return {"mkey": k, "merchant": lc.display_name(rows[-1]), "category": max(cats, key=cats.get),
            "p": round(top / total, 2), "basis": basis[k], "count": len(rows), "typical": amounts[len(amounts) // 2],
            "habit": k in habit_keys,
            "candidates": [{"mkey": kk, "p": round(v / total, 2),
                            "merchant": next((lc.display_name(r) for r in reversed(purchases) if r["_m"] == kk), kk)}
                           for kk, v in ranked[:3]]}


def checkin_text(g, call, when):
    """The words of the check-in: what LEDGER thinks, why, and the smallest possible answer. Unsure, it
    offers its top three instead of betting on one - 'reply 2' is as easy on a Watch as 'y'."""
    hhmm = when.strftime("%I:%M %p").lstrip("0").lower()
    short = lambda name: re.sub(r"\s+-\s+\S*$", "", name).strip()
    c = g.get("candidates") or []
    if g["p"] < 0.6 and len(c) >= 2:
        return "%s purchase - was it  1) %s  2) %s%s ?  Reply 1, 2%s, or say what it was." % (
            hhmm, short(c[0]["merchant"]), short(c[1]["merchant"]), ("  3) %s" % short(c[2]["merchant"])) if len(c) > 2 else "",
            ", 3" if len(c) > 2 else "")
    label = dict((k, lab) for k, lab, _ in lc.INTENTS).get(call.get("intent"), "")
    reason = g["basis"][0] if g.get("basis") else ""
    what = "%s%s" % (g["merchant"], (" - %s" % label.lower()) if label else "")
    return "%s purchase: looks like %s (%s). Right? Reply y or n, or just say what it was." % (hhmm, what, reason)


def read_reply(text):
    """the owner's answer -> (verdict, intent|None). Anything that is not a yes or a no is kept as his words."""
    t = re.sub(r"[^a-z0-9 ']", " ", (text or "").lower()).strip()
    if not t:
        return None, None
    # Pressing play on the shortcut sends Marcus the same blank event a purchase does (first seen 2026-09-17:
    # a manual run was asked about 29 s later). "That was not a purchase" must be sayable, or the phantom tap
    # waits for a statement row and steals a real one's time.
    if re.search(r"\b(test|testing|tested|nothing|ignore|fake|no purchase|not a purchase|did ?n'?t buy|did not buy|pressed play|manual)\b", t):
        return "void", None
    intent = None
    for key, words in (("need", ("need", "needed", "had to")), ("routine", ("routine", "usual", "habit")), ("planned", ("planned", "plan")),
                       ("project", ("project", "build", "parts", "gear")), ("treat", ("treat", "reward")), ("impulse", ("impulse", "impulsive", "whim")),
                       ("social", ("gift", "for someone", "social", "friend", "date", "family"))):
        if any(re.search(r"\b%s\b" % w, t) for w in words):
            intent = key
            break
    first = t.split()[0]
    if first in ("1", "2", "3", "one", "two", "three"):
        return "choice:%d" % ({"one": 1, "two": 2, "three": 3}.get(first) or int(first)), intent
    if first in ("y", "yes", "yep", "yeah", "yup", "right", "correct", "true", "ya", "si"):
        return "confirmed", intent
    if first in ("n", "no", "nope", "nah", "wrong", "false"):
        return ("corrected" if intent or len(t.split()) > 1 else "rejected"), intent
    return "corrected", intent


def center(points):
    """Median point - the owner's range, for judging whether a name resolved to the right branch."""
    if not points:
        return None
    la = sorted(p[0] for p in points)
    lo = sorted(p[1] for p in points)
    return la[len(la) // 2], lo[len(lo) // 2]


# ----------------------------------------------------------------- aggregates
def hour_weekday(rows):
    """rows = purchases with a recovered ts -> 7x24 matrices of count and spend."""
    n = [[0] * 24 for _ in range(7)]
    amt = [[0.0] * 24 for _ in range(7)]
    for r in rows:
        t = datetime.fromtimestamp(r["ts"])
        n[t.weekday()][t.hour] += 1
        amt[t.weekday()][t.hour] += r["amount"]
    return {"count": n, "spent": [[round(v, 2) for v in row] for row in amt]}


def places(rows):
    """Purchases with a merchant position -> one dot per place, with the days money was spent there
    and the smallest / mean / largest single purchase."""
    by = {}
    for r in rows:
        k = (round(r["merchant_lat"], 4), round(r["merchant_lon"], 4))
        p = by.setdefault(k, {"lat": r["merchant_lat"], "lon": r["merchant_lon"], "name": r.get("merchant_place") or r["merchant"],
                              "spent": 0.0, "visits": 0, "merchants": {}, "dates": set(),
                              "smallest": r["amount"], "largest": r["amount"]})
        p["spent"] += r["amount"]
        p["visits"] += 1
        p["smallest"] = min(p["smallest"], r["amount"])
        p["largest"] = max(p["largest"], r["amount"])
        p["merchants"][r["merchant"]] = p["merchants"].get(r["merchant"], 0) + 1
        if r.get("date"):
            p["dates"].add(r["date"])
    out = []
    for p in by.values():
        p["mean"] = round(p["spent"] / p["visits"], 2)
        p["spent"] = round(p["spent"], 2)
        p["merchants"] = sorted(p["merchants"], key=lambda m: -p["merchants"][m])[:4]
        p["dates"] = sorted(p["dates"])
        out.append(p)
    out.sort(key=lambda p: -p["spent"])
    return out


# ------------------------------------------------------------ what goes with it
# Day-level: every purchase has a DATE even when its time is unknown, and sleep, HRV,
# messages, mail and driving are per-day facts - so this works across the whole
# statement, not just the few weeks with GPS.
FEATURES = (
    ("sleep_hours", "Hours slept the night before"), ("sleep_deep_h", "Deep sleep the night before"),
    ("hrv_ms", "HRV that day (higher = more recovered)"), ("resting_hr", "Resting heart rate"),
    ("stress_score", "Stress score"), ("recovery_score", "Recovery score"), ("energy_score", "Energy score"),
    ("steps", "Steps"), ("exercise_min", "Exercise minutes"), ("daylight_min", "Minutes in daylight"),
    ("msgs_in", "Messages received"), ("msgs_out", "Messages sent"), ("msg_people", "People messaged with"),
    ("msgs_late", "Late-night messages (10 pm - 4 am)"), ("mail_promo", "Marketing emails received"),
    ("mail_total", "Emails received"), ("marcus_turns", "Turns with Marcus"), ("video_min", "Minutes of video watched"),
    ("feed_impressions", "Feed posts seen"), ("feed_min", "Minutes in feeds"), ("drive_min", "Minutes driving"),
    ("drive_miles", "Miles driven"),
)
MIN_BUCKET = 8              # nothing is stated about a bucket of fewer days than this
ENOUGH_DAYS = 60            # fewer days behind a signal than this and the page files it under "too early to tell"
BOOTS = 1000                # resamples behind each difference's 90% range
ONE_OFF = 200.0


def day_spend(rows, billed):
    """{date: {'spend', 'count'}} for every calendar day the statements cover - days with no
    purchase are real zeros, days inside a data gap (lc.coverage) are not days at all.
    Only what the owner DECIDES that day: no bills, no billed subscriptions, no one-off
    big-ticket items (a dental crown is not a mood)."""
    purchases = [r for r in rows if r["_k"] == "purchase"]
    if not purchases:
        return {}
    typical = {}
    for r in purchases:
        typical.setdefault(r["_cat"], []).append(r["amount"])
    typical = dict((c, sorted(v)[len(v) // 2]) for c, v in typical.items())
    out, one = {}, __import__("datetime").timedelta(days=1)
    for a, b in lc.coverage(rows):
        dd = max(a, purchases[0]["_d"])
        while dd <= min(b, purchases[-1]["_d"]):
            out[dd.isoformat()] = {"spend": 0.0, "count": 0}
            dd += one
    for r in purchases:
        if r["date"] not in out:
            continue
        if (r["_cat"] in lc.NOT_A_LEVER or r.get("uid") in billed
                or (r["amount"] >= ONE_OFF and r["amount"] > 4 * typical[r["_cat"]])):
            continue
        out[r["date"]]["spend"] += r["amount"]
        out[r["date"]]["count"] += 1
    return out


def _perm_p(a, b, shuffles, rnd):
    """Two-sided permutation p-value for a difference in means."""
    obs = abs(sum(a) / len(a) - sum(b) / len(b))
    pool, na, hits = a + b, len(a), 0
    for _ in range(shuffles):
        rnd.shuffle(pool)
        if abs(sum(pool[:na]) / na - sum(pool[na:]) / (len(pool) - na)) >= obs - 1e-12:
            hits += 1
    return (hits + 1.0) / (shuffles + 1.0)


def drivers(spend_by_day, features_by_day, shuffles=2000, seed=1):
    """For each signal: spending on the days it ran HIGH against the days it ran LOW (split
    at the owner's own median), with a permutation test. A day missing the signal is left
    out of that signal - absent is never zero. Returns every signal tested, ordered by
    how hard the difference is to get by chance; the caller must show n and p.
    `range_lo`..`range_hi` is a 90% bootstrap range for the difference: a range that
    crosses zero is the plain-words way to say "could be chance"."""
    import random
    rnd = random.Random(seed)
    brnd = random.Random(seed + 1)          # its own stream: adding the range must not move any p
    out = []
    for key, label in FEATURES:
        pts = [(features_by_day[d][key], spend_by_day[d]["spend"], spend_by_day[d]["count"])
               for d in spend_by_day if d in features_by_day and features_by_day[d].get(key) is not None]
        if len(pts) < 2 * MIN_BUCKET:
            continue
        vals = sorted(x[0] for x in pts)
        med = vals[len(vals) // 2]
        lo = [x for x in pts if x[0] < med] or [x for x in pts if x[0] <= med]
        hi = [x for x in pts if x not in lo]
        if len(lo) < MIN_BUCKET or len(hi) < MIN_BUCKET:
            continue
        ml, mh = sum(x[1] for x in lo) / len(lo), sum(x[1] for x in hi) / len(hi)
        p = _perm_p([x[1] for x in hi], [x[1] for x in lo], shuffles, rnd)
        days_ = sorted(d for d in spend_by_day if d in features_by_day and features_by_day[d].get(key) is not None)
        hv, lv, diffs = [x[1] for x in hi], [x[1] for x in lo], []
        for _ in range(BOOTS):
            a, b = brnd.choices(hv, k=len(hv)), brnd.choices(lv, k=len(lv))
            diffs.append(sum(a) / len(a) - sum(b) / len(b))
        diffs.sort()
        out.append({"key": key, "label": label, "split_at": med, "n_low": len(lo), "n_high": len(hi),
                    "range_lo": round(diffs[int(BOOTS * .05)], 2), "range_hi": round(diffs[int(BOOTS * .95) - 1], 2),
                    "enough": len(pts) >= ENOUGH_DAYS, "enough_days": ENOUGH_DAYS,
                    "spend_low": round(ml, 2), "spend_high": round(mh, 2), "diff": round(mh - ml, 2),
                    "count_low": round(sum(x[2] for x in lo) / float(len(lo)), 2),
                    "count_high": round(sum(x[2] for x in hi) / float(len(hi)), 2),
                    "p": round(p, 4), "from": days_[0], "to": days_[-1],
                    "verdict": "clear" if p < 0.01 else "suggestive" if p < 0.05 else "no difference"})
    out.sort(key=lambda x: x["p"])
    return out


def weekday_profile(spend_by_day):
    from datetime import date as _date
    tot, n = [0.0] * 7, [0] * 7
    for d, v in spend_by_day.items():
        w = _date(int(d[:4]), int(d[5:7]), int(d[8:10])).weekday()
        tot[w] += v["spend"]
        n[w] += 1
    return [{"weekday": i, "days": n[i], "mean_spend": round(tot[i] / n[i], 2) if n[i] else 0.0} for i in range(7)]


# ------------------------------------------------------------------------ I/O
SCHEMA = """
CREATE TABLE IF NOT EXISTS merchant_geo (
    mkey TEXT NOT NULL, zip TEXT NOT NULL, lat REAL, lon REAL, resolved TEXT, source TEXT, at TEXT, kind TEXT,
    PRIMARY KEY (mkey, zip));
CREATE TABLE IF NOT EXISTS days (date TEXT PRIMARY KEY, features TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS receipts (uid TEXT PRIMARY KEY, ts REAL NOT NULL, matched TEXT, domain TEXT);
CREATE TABLE IF NOT EXISTS analysis (key TEXT PRIMARY KEY, value TEXT NOT NULL, built_at TEXT);
CREATE TABLE IF NOT EXISTS checkins (
    tap_id INTEGER PRIMARY KEY, epoch REAL NOT NULL, created_at TEXT, merchant TEXT, mkey TEXT, category TEXT,
    intent TEXT, confidence REAL, basis TEXT, text TEXT, state TEXT, sent_at TEXT, reply TEXT, reply_at TEXT,
    verdict TEXT, reply_intent TEXT, uid TEXT, candidates TEXT, reply_mkey TEXT);
CREATE TABLE IF NOT EXISTS purchase_context (uid TEXT PRIMARY KEY, ctx TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS intents (uid TEXT PRIMARY KEY, intent TEXT, confidence REAL, prompted_by TEXT,
    evidence TEXT, runner_up TEXT, built_at TEXT);
CREATE TABLE IF NOT EXISTS moments (
    uid TEXT PRIMARY KEY, channel TEXT, ts REAL, ts_lo REAL, ts_hi REAL, time_source TEXT,
    merchant_lat REAL, merchant_lon REAL, merchant_place TEXT, geo_source TEXT,
    david_lat REAL, david_lon REAL, david_place TEXT, evidence TEXT, built_at TEXT);
"""


def _geo():
    """polaris-server's offline geocoder, imported from its own repo. None if it is not there."""
    try:
        if str(POLARIS) not in sys.path:
            sys.path.insert(0, str(POLARIS))
        import geo                                  # noqa: E402
        return lambda name, bias: geo.geocode(name, bias=bias)
    except Exception as e:
        sys.stderr.write("geocoder unavailable: %r\n" % (e,))
        return None


def _city_lookup():
    """description -> (lat, lon, radius_km, name) of the town the STATEMENT names ("... SPRINGFIELD 12345 XX USA"),
    or None. The geocoder indexes names, so a merchant can resolve to a namesake 33 km away (the cafe:
    the home town on the statement, the next town in the index). The statement's town is the referee."""
    p = POLARIS / "geo.sqlite"
    if not p.exists():
        return lambda description, bias: None
    con = sqlite3.connect("file:%s?mode=ro" % p, uri=True, timeout=10, check_same_thread=False)
    rx = re.compile(r"((?:[A-Z][A-Z.'-]*\s+){0,2}[A-Z][A-Z.'-]*)\s*\d{5}(?:-\d{4})?\s*[A-Z]{2}\s+(?:USA?|US)\s*$")
    radius = {"place:city": 16.0, "place:town": 8.0, "place:suburb": 6.0, "place:village": 5.0}
    cache = {}

    def look(description, bias):
        m = rx.search((description or "").upper().strip())
        if not m:
            return None
        words = m.group(1).split()
        for n in (3, 2, 1):
            name = " ".join(words[-n:]).lower()
            if name not in cache:
                rows = con.execute("SELECT lat, lon, kind, name FROM geo WHERE norm = ? AND kind IN ('place:city','place:town','place:suburb','place:village')", (name,)).fetchall()
                rows.sort(key=lambda r: km((r[0], r[1]), bias) if bias else 0)
                cache[name] = (rows[0][0], rows[0][1], radius[rows[0][2]], rows[0][3]) if rows else None
            if cache[name]:
                return cache[name]
        return None
    return look


def _branch_lookup():
    """(merchant, description, city) -> (cands, anchors) for pick_branch(), read straight from the geocoder's index.
    `city` is _city_lookup()'s answer: (lat, lon, radius_km, name)."""
    p = POLARIS / "geo.sqlite"
    if not p.exists():
        return lambda merchant, description, city: ([], [])
    con = sqlite3.connect("file:%s?mode=ro" % p, uri=True, timeout=10, check_same_thread=False)
    norm = lambda x: re.sub(r"[^a-z0-9]+", " ", (x or "").lower().replace("'", "").replace("\u2019", "")).split()

    def rows(terms, city):
        w = city[2] / 111.0 + 0.02
        try:
            return con.execute("SELECT g.name, g.city, g.kind, g.lat, g.lon FROM geo_fts f JOIN geo g ON g.id = f.rowid WHERE geo_fts MATCH ? "
                               "AND g.lat BETWEEN ? AND ? AND g.lon BETWEEN ? AND ? LIMIT 600",
                               (" ".join('"%s"*' % t for t in terms), city[0] - w, city[0] + w, city[1] - w * 1.3, city[1] + w * 1.3)).fetchall()
        except sqlite3.Error:
            return []

    memo = {}

    def look(merchant, description, city):
        key = (merchant, description, city[3])
        if key not in memo:             # one answer per branch, not per visit to it
            memo[key] = find(merchant, description, city)
        return memo[key]

    def find(merchant, description, city):
        cands, seen = [], set()
        for v in name_variants(merchant):
            for name, town, kind, la, lo in rows(norm(v), city) if norm(v) else []:
                label = name if not town or " ".join(norm(town)) in " ".join(norm(name)) else "%s, %s" % (name, town)
                if (round(la, 4), round(lo, 4)) in seen or (kind or "").startswith(NOT_A_SHOP) or not solid(merchant, label, city[3]):
                    continue
                if km((la, lo), (city[0], city[1])) <= city[2]:
                    seen.add((round(la, 4), round(lo, 4)))
                    cands.append((la, lo, label))
            if cands:
                break                   # the fullest name that resolves is the one to trust
        street = street_of(description, city[3]) if len(cands) > 1 else None
        anchors = []
        if street:
            for name, _, _, la, lo in rows(street, city):
                words = norm(name)
                if all(any(w.startswith(t) for w in words) for t in street):       # the name's own words, not the city column
                    anchors.append((la, lo))
        return cands, anchors
    return look


def _kind_lookup():
    """(lat, lon) -> OSM kind, straight from the geocoder's index."""
    p = POLARIS / "geo.sqlite"
    if not p.exists():
        return lambda la, lo: None
    con = sqlite3.connect("file:%s?mode=ro" % p, uri=True, timeout=10, check_same_thread=False)

    def look(la, lo):
        r = con.execute("SELECT kind FROM geo WHERE abs(lat-?)<1e-6 AND abs(lon-?)<1e-6 LIMIT 1", (la, lo)).fetchone()
        return r[0] if r else None
    return look


def _polaris_day_stops():
    """{date: [stop]} from Mapblock's visits + GPS-gap stops. Real data only (trips 1-80 are seed)."""
    p = POLARIS / "polaris.db"
    if not p.exists():
        return {}
    con = sqlite3.connect("file:%s?mode=ro" % p, uri=True, timeout=10)
    try:
        visits = [{"arrive": a, "depart": d, "lat": la, "lon": lo, "place": pl, "src": "visit"}
                  for a, d, la, lo, pl in con.execute("SELECT arrive_ts, depart_ts, lat, lon, place FROM visits ORDER BY arrive_ts")]
        first = min([v["arrive"] for v in visits] or [0])
        fixes = [tuple(r) for r in con.execute("SELECT ts, lat, lon FROM fixes WHERE ts >= ? ORDER BY ts", (first - 86400 * 3,))]
    finally:
        con.close()
    days = {}
    for s in merge_stops(visits, stops_from_fixes(fixes)):
        days.setdefault(datetime.fromtimestamp(s["arrive"]).strftime("%Y-%m-%d"), []).append(s)
    return days


def _polaris_day_drives():
    """{date: {'drive_min','drive_miles'}} from Mapblock's real trips (ids 1-80 are seed data)."""
    p = POLARIS / "polaris.db"
    if not p.exists():
        return {}
    con = sqlite3.connect("file:%s?mode=ro" % p, uri=True, timeout=10)
    out = {}
    try:
        for a, b, m in con.execute("SELECT start_ts, end_ts, distance_m FROM trips WHERE synthetic = 0 AND end_ts IS NOT NULL"):
            d = out.setdefault(datetime.fromtimestamp(a).strftime("%Y-%m-%d"), {"drive_min": 0.0, "drive_miles": 0.0})
            d["drive_min"] += (b - a) / 60.0
            d["drive_miles"] += (m or 0.0) / 1609.344
    except sqlite3.Error:
        pass
    finally:
        con.close()
    return dict((k, {"drive_min": round(v["drive_min"], 1), "drive_miles": round(v["drive_miles"], 1)}) for k, v in out.items())


def latest_fix(epoch):
    """(lat, lon, age_seconds) of Mapblock's newest GPS fix relative to `epoch`, or None. The phone uploads
    in batches - on 2026-09-17 the newest fix was 67 minutes old when a tap arrived - so age is part of the answer."""
    p = POLARIS / "polaris.db"
    if not p.exists():
        return None
    try:
        con = sqlite3.connect("file:%s?mode=ro" % p, uri=True, timeout=5)
        try:
            r = con.execute("SELECT ts, lat, lon FROM fixes WHERE ts <= ? + 120 ORDER BY ts DESC LIMIT 1", (epoch,)).fetchone()
        finally:
            con.close()
    except sqlite3.Error:
        return None
    return (r[1], r[2], max(0.0, epoch - r[0])) if r else None


def build(verbose=True):
    conn = sqlite3.connect(str(DB), timeout=20)
    conn.row_factory = sqlite3.Row
    conn.executescript(SCHEMA)
    if "kind" not in set(r[1] for r in conn.execute("PRAGMA table_info(merchant_geo)")):
        conn.execute("ALTER TABLE merchant_geo ADD COLUMN kind TEXT")
    aliases = dict((r["raw"], r["alias"]) for r in conn.execute("SELECT raw, alias FROM merchant_alias"))
    try:
        overrides = dict((r["uid"], r["category"]) for r in conn.execute("SELECT uid, category FROM enrich WHERE category IS NOT NULL"))
    except sqlite3.Error:
        overrides = {}
    rows = lc.prepare([dict(r) for r in conn.execute("SELECT * FROM transactions")], aliases, overrides)
    purchases = [r for r in rows if r["_k"] == "purchase"]
    today = datetime.now().date()
    billed = set(u for s in lc.recurring(rows, today) for u in s["uids"])
    geocode = _geo()
    day_stops = _polaris_day_stops()
    home = center([(s["lat"], s["lon"]) for ss in day_stops.values() for s in ss])

    out = {}
    for r in purchases:
        hint = lc.place_hint(r.get("description"))
        out[r["uid"]] = {"channel": channel(r, hint, r["uid"] in billed), "_hint": hint, "_row": r}

    # WHEN + WHERE together, for days with a recorded track
    by_day = {}
    for r in purchases:
        if out[r["uid"]]["channel"] == "in_person":
            by_day.setdefault(r["date"], []).append(r)
    matched = 0
    if geocode:
        for day, ps in by_day.items():
            for uid, m in match_day(ps, day_stops.get(day, []), geocode).items():
                out[uid].update(m)
                matched += 1

    # Wallet taps: the purchase moment to the second (needs the conn's taps table, mirrored from Marcus)
    try:
        taps = [dict(r) for r in conn.execute("SELECT t.id, t.epoch, t.blank, t.amount, t.merchant, c.reply_mkey AS said_mkey "
                                               "FROM taps t LEFT JOIN checkins c ON c.tap_id = t.id "
                                               "WHERE t.epoch IS NOT NULL AND COALESCE(c.verdict, '') != 'void'")]     # he said it was not a purchase
    except sqlite3.Error:
        taps = []
    tapped, unpaired = pair_taps(taps, [r for r in purchases if out[r["uid"]]["channel"] == "in_person"], day_stops, geocode)
    for uid, m in tapped.items():
        keep = dict((k, v) for k, v in out[uid].items() if k.startswith(("merchant_", "david_", "geo_")) and k not in m)
        ev = dict(out[uid].get("evidence") or {}, **m["evidence"])
        out[uid].update(m)
        out[uid].update(keep)
        out[uid]["evidence"] = ev

    for uid, m in tapped.items():
        tid = (m.get("evidence") or {}).get("tap_id")
        if tid is not None:
            conn.execute("UPDATE checkins SET uid = ? WHERE tap_id = ? AND uid IS NULL", (uid, tid))
    for ck in conn.execute("SELECT uid, intent, verdict, reply_intent FROM checkins WHERE uid IS NOT NULL AND verdict IN ('confirmed','corrected')").fetchall():
        said = ck["reply_intent"] or (ck["intent"] if ck["verdict"] == "confirmed" else None)
        if said:        # his word on the Watch is his correction/confirmation of that row - never overwrite one he made by hand
            conn.execute("INSERT INTO enrich(uid, intent, intent_at, updated_at) VALUES (?,?,?,?) "
                         "ON CONFLICT(uid) DO UPDATE SET intent = excluded.intent, intent_at = excluded.intent_at WHERE enrich.intent IS NULL",
                         (ck["uid"], said, datetime.now().astimezone().isoformat(timespec="seconds"), datetime.now().astimezone().isoformat(timespec="seconds")))
    conn.commit()

    # the minute a receipt mail arrived (vr-2 finds these; only the timestamp and sender domain come here).
    # A stop-match keeps its place; a receipt inside or near that stop sharpens its time, one far from it loses.
    for rc in conn.execute("SELECT uid, ts, matched, domain FROM receipts"):
        m = out.get(rc["uid"])
        if m is None:
            continue
        if m.get("time_source") == "tap":
            continue                                   # nothing beats the tap itself
        if m.get("ts") is None or (m["ts_lo"] - 1800 <= rc["ts"] <= m["ts_hi"] + 1800):
            m.update(ts=rc["ts"], time_source="receipt", ts_lo=m.get("ts_lo") or rc["ts"], ts_hi=m.get("ts_hi") or rc["ts"])
            m["evidence"] = dict(m.get("evidence") or {}, receipt=rc["matched"], receipt_from=rc["domain"])

    # WHERE alone, for everything else in person: the name, near his range, remembered per (merchant, zip)
    known = dict(((r["mkey"], r["zip"]), dict(r)) for r in conn.execute("SELECT * FROM merchant_geo"))
    for uid, m in out.items():
        r, hint = m["_row"], m["_hint"]
        if m["channel"] != "in_person" or "merchant_lat" in m:
            if "merchant_lat" in m and hint:                    # a stop-match is the best fix this merchant will get
                known[(r["_m"], hint["zip"])] = {"mkey": r["_m"], "zip": hint["zip"], "lat": m["merchant_lat"],
                                                  "lon": m["merchant_lon"], "resolved": m["merchant_place"], "source": "stop-match"}
            continue
    city_of = _city_lookup()
    kind_of = _kind_lookup()
    branch_of = _branch_lookup()
    in_zip, states = {}, {}
    for g in known.values():            # what a real stop already pinned, by ZIP: the referee for a branch
        if g.get("source") == "stop-match" and g.get("lat") is not None:
            in_zip.setdefault(g["zip"], []).append((g["lat"], g["lon"]))
    for m in out.values():
        if m["channel"] == "in_person" and m["_hint"]:
            states[m["_hint"]["state"]] = states.get(m["_hint"]["state"], 0) + 1
    # The index is one state's map. A line from another state can only resolve to a namesake: a firm in a Springfield
    # two thousand miles away was pinned to the Springfield in his own state. Those stay unplaced.
    home_state = max(sorted(states), key=states.get) if states else None
    # A hotel prints its reservations phone where the town goes ("HOTEL ... 800-555-0100 12345 XX USA"). The same
    # ZIP on his OTHER lines names the town (12345 -> SPRINGFIELD): his own statements are the ZIP table.
    # Most common tail first, and only a tail that names a real town counts ("... FLOOR INTERNET 12345" does not); a ZIP
    # none of his lines names falls back to its first three digits - one postal area (123xx = one sectional centre).
    tails5, tails3, zip_city = {}, {}, {}
    for r in rows:
        line = (r.get("description") or "").upper().strip()
        zm = ZIP_TAIL.search(line)
        if zm and not PHONE_FOR_TOWN.search(line):
            for d, key in ((tails5, zm.group(2)), (tails3, zm.group(2)[:3])):
                t = d.setdefault(key, {})
                t[zm.group(0)] = t.get(zm.group(0), 0) + 1

    def town_of_zip(z):
        if z not in zip_city:
            zip_city[z] = None
            for d, key in ((tails5, z), (tails3, z[:3])):
                for tail in sorted(d.get(key, {}), key=lambda t: (-d[key][t], t)):
                    zip_city[z] = city_of(tail, home)
                    if zip_city[z]:
                        return zip_city[z]
        return zip_city[z]
    for uid, m in out.items():
        r, hint = m["_row"], m["_hint"]
        if m["channel"] != "in_person" or "merchant_lat" in m or not hint:
            continue
        k = (r["_m"], hint["zip"])
        if geocode and home and (k not in known or known[k].get("source") in ("name", "unresolved", "city-area")):
            phone = bool(PHONE_FOR_TOWN.search((r.get("description") or "").upper().strip()))
            city = None if hint["state"] != home_state else (
                town_of_zip(hint["zip"]) if phone else city_of(r.get("description"), home))
            away = hint["state"] != home_state or (phone and not city)      # no town on the line and none from its ZIP: nowhere to look, and near HOME is a guess
            merchant = r.get("merchant") or r["_m"]
            g = None
            if city:
                b = pick_branch(*branch_of(merchant, r.get("description"), city), zip_anchor=center(in_zip.get(hint["zip"]) or []))
                if b:
                    g = {"lat": b[0], "lon": b[1], "name": b[2]}
            else:
                b = None
            for bias in [] if g or b is False or away else ([(city[0], city[1])] if city else []) + [home]:      # look where the statement says first
                for v in name_variants(merchant):
                    c = geocode(v, bias)
                    # near is not enough: a namesake next door is still the wrong place (the town pin is honest)
                    if c and (not solid(merchant, c["name"], city[3] if city else None) or (kind_of(c["lat"], c["lon"]) or "").startswith(NOT_A_SHOP)):
                        continue
                    if c and (km((c["lat"], c["lon"]), (city[0], city[1])) <= city[2] if city else km((c["lat"], c["lon"]), home) <= LOCAL_KM):
                        g = c
                        break
                if g:
                    break
            if g:
                known[k] = {"mkey": k[0], "zip": k[1], "lat": g["lat"], "lon": g["lon"], "resolved": g["name"], "source": "name"}
            elif city:        # not in the index, or only a namesake elsewhere: the town itself, and say it is approximate
                known[k] = {"mkey": k[0], "zip": k[1], "lat": city[0], "lon": city[1], "resolved": "%s (area)" % city[3], "source": "city-area"}
            else:
                known[k] = {"mkey": k[0], "zip": k[1], "lat": None, "lon": None, "resolved": None, "source": "unresolved"}
        g = known.get(k)
        if g and g.get("lat") is not None:
            m.update(merchant_lat=g["lat"], merchant_lon=g["lon"], merchant_place=g["resolved"], geo_source=g["source"])

    now = datetime.now().astimezone().isoformat(timespec="seconds")
    with conn:
        conn.execute("DELETE FROM moments")
        conn.executemany(
            "INSERT INTO moments(uid,channel,ts,ts_lo,ts_hi,time_source,merchant_lat,merchant_lon,merchant_place,geo_source,"
            "david_lat,david_lon,david_place,evidence,built_at) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            [(uid, m["channel"], m.get("ts"), m.get("ts_lo"), m.get("ts_hi"), m.get("time_source"), m.get("merchant_lat"),
              m.get("merchant_lon"), m.get("merchant_place"), m.get("geo_source"), m.get("david_lat"), m.get("david_lon"),
              m.get("david_place"), json.dumps(m["evidence"]) if m.get("evidence") else None, now) for uid, m in out.items()])
        names = dict((r["_m"], r.get("merchant") or r["_m"]) for r in purchases)
        live = set((m["_row"]["_m"], m["_hint"]["zip"]) for m in out.values() if m["channel"] == "in_person" and m["_hint"])
        for k in [k for k, g in known.items() if k not in live and g.get("source") in ("name", "city-area", "unresolved")]:
            conn.execute("DELETE FROM merchant_geo WHERE mkey = ? AND zip = ?", k)      # a web order once read as a shop visit: its pin must not outlive the mistake
            del known[k]
        for g in known.values():
            kind = None
            if g.get("lat") is not None and solid(names.get(g["mkey"], g["mkey"]), g.get("resolved")):
                kind = kind_of(g["lat"], g["lon"])
            conn.execute("INSERT OR REPLACE INTO merchant_geo(mkey,zip,lat,lon,resolved,source,at,kind) VALUES (?,?,?,?,?,?,?,?)",
                         (g["mkey"], g["zip"], g.get("lat"), g.get("lon"), g.get("resolved"), g.get("source"), g.get("at") or now, kind))
    # what goes with spending more: day-level, in the background (2000 shuffles per signal is too slow for a request)
    feats = dict((r["date"], json.loads(r["features"])) for r in conn.execute("SELECT date, features FROM days"))
    for d, v in _polaris_day_drives().items():
        feats.setdefault(d, {}).update(v)
    spend = day_spend(rows, billed)
    tracked = [d for d in feats if "drive_min" in feats[d]]
    if tracked:                                  # within Mapblock's era a day with no trip is a real zero, not a missing value
        for d in spend:
            if min(tracked) <= d <= max(tracked):
                feats.setdefault(d, {}).setdefault("drive_min", 0.0)
                feats[d].setdefault("drive_miles", 0.0)
    result = {"drivers": drivers(spend, feats), "weekday": weekday_profile(spend), "days": len(spend),
              "from": min(spend) if spend else None, "to": max(spend) if spend else None,
              "mean_spend": round(sum(v["spend"] for v in spend.values()) / len(spend), 2) if spend else 0.0}
    # WHY, inferred: every purchase, from whatever is on record for it
    ctx = dict((r["uid"], json.loads(r["ctx"])) for r in conn.execute("SELECT uid, ctx FROM purchase_context"))
    habit_keys = set(h["merchant"] for h in lc.habits(rows, today))
    by_m, first_seen = {}, {}
    for r in purchases:
        by_m.setdefault(r["_m"], []).append(r)
        first_seen.setdefault(r["_m"], r)
    med = lambda v: sorted(v)[len(v) // 2]
    typical = dict((k, med([r["amount"] for r in v])) for k, v in by_m.items())
    hours = {}
    for uid, m in out.items():
        if m.get("ts"):
            hours.setdefault(m["_row"]["_m"], []).append(datetime.fromtimestamp(m["ts"]).hour)
    sleeps = sorted(f["sleep_hours"] for f in feats.values() if f.get("sleep_hours") is not None)
    stress = sorted(f["stress_score"] for f in feats.values() if f.get("stress_score") is not None)
    sleep_med = sleeps[len(sleeps) // 2] if len(sleeps) >= 8 else None
    stress_hi = stress[int(len(stress) * .75)] if len(stress) >= 8 else None
    cov = lc.coverage(rows)
    seen_before = lambda d: lc.covered_days(cov, d - timedelta(days=60), d) >= 60    # 60 OBSERVED days before it, not a gap
    calls = []
    for uid, m in out.items():
        r = m["_row"]
        c, f = ctx.get(uid, {}), feats.get(r["date"], {})
        n, t = len(by_m[r["_m"]]), typical[r["_m"]]
        facts = dict(c, category=r["_cat"], amount=r["amount"], channel=m["channel"], habit=r["_m"] in habit_keys,
                     merchant_count=n, typical=t, usual_amount=bool(n >= 4 and t and abs(r["amount"] - t) <= 0.25 * t),
                     first_time=bool(first_seen[r["_m"]] is r and seen_before(r["_d"])))
        if m.get("ts"):
            h = datetime.fromtimestamp(m["ts"])
            hs = hours.get(r["_m"], [])
            facts.update(hour=h.hour, weekday=h.weekday(), usual_hour=bool(len(hs) >= 5 and abs(h.hour - med(hs)) <= 2))
        if sleep_med is not None and f.get("sleep_hours") is not None:
            facts["short_sleep"] = f["sleep_hours"] < sleep_med - 1.0
        if stress_hi is not None and f.get("stress_score") is not None:
            facts["high_stress"] = f["stress_score"] >= stress_hi
        if f.get("exercise_min") is not None:
            facts["worked_out"] = f["exercise_min"] >= 20
        call = infer_intent(facts)
        calls.append((uid, call["intent"], call["confidence"], call["prompted_by"], json.dumps(call["evidence"]), call.get("runner_up"), now))
    with conn:
        conn.execute("DELETE FROM intents")
        conn.executemany("INSERT INTO intents(uid,intent,confidence,prompted_by,evidence,runner_up,built_at) VALUES (?,?,?,?,?,?,?)", calls)
        conn.execute("INSERT OR REPLACE INTO analysis(key, value, built_at) VALUES ('taps', ?, ?)",
                     (json.dumps({"stored": len(taps), "paired": len(tapped), "waiting_for_statement": len(unpaired)}), now))
        conn.execute("INSERT OR REPLACE INTO analysis(key, value, built_at) VALUES ('drivers', ?, ?)", (json.dumps(result), now))
    conn.close()
    n = len(out)
    stats = {"purchases": n, "in_person": sum(1 for m in out.values() if m["channel"] == "in_person"),
             "online": sum(1 for m in out.values() if m["channel"] == "online"),
             "billed": sum(1 for m in out.values() if m["channel"] == "billed"),
             "placed": sum(1 for m in out.values() if m.get("merchant_lat") is not None),
             "timed": sum(1 for m in out.values() if m.get("ts")), "signals_tested": len(result["drivers"]),
             "taps_paired": len(tapped), "intents": dict((k, sum(1 for c in calls if c[1] == k)) for k in set(c[1] for c in calls)),
             "track_days": len(day_stops),
             "track_from": min(day_stops) if day_stops else None}
    if verbose:
        print(json.dumps(stats))
    return stats


if __name__ == "__main__":
    build()
