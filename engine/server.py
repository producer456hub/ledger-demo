#!/usr/bin/python3
"""LEDGER — the fleet's spending instrument.

Self-contained: Python stdlib only (http.server + sqlite3), 3.9 syntax. Binds
loopback on :8945 and is fronted by `tailscale serve --https=8945`, so every
client reaches it as https://ledger.example:8945/.

WHO MAY READ. There is no PIN and no token. `tailscale serve` stamps each
proxied request with the tailnet identity of the device that made it
(`Tailscale-User-Login`), strips any copy a client tried to send, and is the
only way in from the network because the socket is loopback-only. LEDGER
answers when that login is OWNER. The credential is each device's own tailnet
node key - Tailscale issues and rotates it; nothing is stored on a client.
A request that never went through the proxy (no X-Forwarded-* at all) is a
process on this Mac - the DOCKET sweep, a test - and is trusted like the
database file it could read anyway.

WHERE THE DATA COMES FROM. Marcus on vr-2 stays the system of record
(C:\\Users\\owner\\.marcus\\spending.sqlite: Apple Card statement imports plus
Wallet-tap events). vr-2's ledger_push.py POSTs a full snapshot here whenever
it changes; `transactions` is replaced wholesale, so the mirror is exact even
when a statement row supersedes a provisional tap row. Everything the owner adds
here (notes, category overrides, reviewed flags, aliases, budgets) lives in
separate tables keyed by uid and survives every snapshot.
"""
import json
import os
import re
import sqlite3
import sys
import threading
from datetime import date, datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse, parse_qs, unquote

import ledger_core as lc
import motive

HERE = Path(__file__).resolve().parent
DB = Path(os.environ.get("LEDGER_DB") or (HERE / "ledger.db"))
PORT = int(os.environ.get("LEDGER_PORT", "8945"))
BIND = os.environ.get("LEDGER_BIND", "127.0.0.1")
OWNER = os.environ.get("LEDGER_OWNER", "owner@example.com").strip().lower()
SHELL_ORIGIN = os.environ.get("LEDGER_SHELL_ORIGIN", "https://ledger.example:8940")
MARCUS = os.environ.get("LEDGER_MARCUS", "https://marcus.example").rstrip("/")
VERSION = "0.2.0"

_lock = threading.Lock()
_cache = {"version": 0, "built": -1, "rows": []}

SCHEMA = """
PRAGMA journal_mode=WAL;
CREATE TABLE IF NOT EXISTS transactions (
    uid TEXT PRIMARY KEY, date TEXT NOT NULL, posted TEXT, amount REAL NOT NULL,
    merchant TEXT, description TEXT, category TEXT, kind TEXT, card TEXT, ref TEXT,
    source TEXT, imported_at TEXT);
CREATE INDEX IF NOT EXISTS tx_date ON transactions(date);
CREATE TABLE IF NOT EXISTS enrich (
    uid TEXT PRIMARY KEY, note TEXT, category TEXT, awaiting_refund TEXT, updated_at TEXT);
CREATE TABLE IF NOT EXISTS reviewed (flag_id TEXT PRIMARY KEY, at TEXT);
CREATE TABLE IF NOT EXISTS merchant_alias (raw TEXT PRIMARY KEY, alias TEXT NOT NULL, at TEXT);
CREATE TABLE IF NOT EXISTS budgets (category TEXT PRIMARY KEY, target REAL NOT NULL, goal_item INTEGER, at TEXT);
CREATE TABLE IF NOT EXISTS nudge_settings (kind TEXT PRIMARY KEY, enabled INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS nudge_log (id TEXT PRIMARY KEY, kind TEXT, text TEXT, sent_at TEXT, state TEXT);
CREATE TABLE IF NOT EXISTS plan (lever_id TEXT PRIMARY KEY, value REAL NOT NULL, at TEXT);
CREATE TABLE IF NOT EXISTS taps (
    id INTEGER PRIMARY KEY, ts TEXT NOT NULL, epoch REAL, ip TEXT, blank INTEGER, amount TEXT, merchant TEXT);
CREATE TABLE IF NOT EXISTS push_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT, at TEXT, host TEXT, who TEXT, rows INTEGER,
    added INTEGER, removed INTEGER, signature TEXT, marcus_status TEXT);
"""
TX_COLS = ("uid", "date", "posted", "amount", "merchant", "description", "category",
           "kind", "card", "ref", "source", "imported_at")


def now_iso():
    return datetime.now().astimezone().isoformat(timespec="seconds")


def _db():
    conn = sqlite3.connect(str(DB), timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA busy_timeout=10000")
    return conn


def init_db():
    conn = _db()
    try:
        conn.executescript(SCHEMA)
        conn.executescript(motive.SCHEMA)
        for table, cols in (("taps", ("lat", "lon", "acc")), ("checkins", ("candidates", "reply_mkey"))):
            have = set(r[1] for r in conn.execute("PRAGMA table_info(%s)" % table))
            for c in cols:
                if c not in have:
                    conn.execute("ALTER TABLE %s ADD COLUMN %s %s" % (table, c, "REAL" if table == "taps" else "TEXT"))
        if "kind" not in set(r[1] for r in conn.execute("PRAGMA table_info(merchant_geo)")):
            conn.execute("ALTER TABLE merchant_geo ADD COLUMN kind TEXT")
        cols = set(r[1] for r in conn.execute("PRAGMA table_info(enrich)"))
        if "intent" not in cols:               # the owner's CORRECTION of an inferred intent (see MOTIVE.md) - never a survey
            conn.execute("ALTER TABLE enrich ADD COLUMN intent TEXT")
            conn.execute("ALTER TABLE enrich ADD COLUMN intent_at TEXT")
        conn.commit()
    finally:
        conn.close()


def _touch():
    with _lock:
        _cache["version"] += 1


_motive_kick = threading.Event()


def _motive_loop():
    """WHERE and WHEN (motive.py), rebuilt after every snapshot, at start, and every 30 minutes
    because Mapblock keeps recording stops. In-process so the dataset cache can be invalidated."""
    _motive_kick.set()
    while True:
        _motive_kick.wait(timeout=1800)
        _motive_kick.clear()
        try:
            stats = motive.build(verbose=False)
            _touch()
            print("motive: %s" % json.dumps(stats), flush=True)
        except Exception as e:
            sys.stderr.write("motive build failed: %r\n" % (e,))


# ------------------------------------------------------------------ dataset
class Data(object):
    """Everything one request needs, computed once per change to the database."""

    def __init__(self, conn):
        self.aliases = dict((r["raw"], r["alias"]) for r in conn.execute("SELECT raw, alias FROM merchant_alias"))
        self.enrich = dict((r["uid"], dict(r)) for r in conn.execute("SELECT * FROM enrich"))
        overrides = dict((u, e["category"]) for u, e in self.enrich.items() if e.get("category"))
        raw = [dict(r) for r in conn.execute("SELECT * FROM transactions")]
        # the map's kind of place, kept only for solid name matches (motive.solid) - the categorizer's third layer
        kinds = dict((r["mkey"], r["kind"]) for r in conn.execute("SELECT mkey, kind FROM merchant_geo WHERE kind IS NOT NULL"))
        self.rows = lc.prepare(raw, self.aliases, overrides, kinds)
        self.reviewed = set(r["flag_id"] for r in conn.execute("SELECT flag_id FROM reviewed"))
        self.awaiting = dict((u, e["awaiting_refund"]) for u, e in self.enrich.items() if e.get("awaiting_refund"))
        self.corrections = dict((u, e["intent"]) for u, e in self.enrich.items() if e.get("intent"))
        self.inferred = dict((r["uid"], {"intent": r["intent"], "confidence": r["confidence"], "prompted_by": r["prompted_by"],
                                           "evidence": json.loads(r["evidence"] or "[]"), "runner_up": r["runner_up"]})
                             for r in conn.execute("SELECT * FROM intents"))
        # what the page and the sums use: the owner's correction where he made one, else the inference
        self.intents = dict((u, i["intent"]) for u, i in self.inferred.items() if i["intent"])
        self.intents.update(self.corrections)
        judged = [u for u in self.corrections if u in self.inferred]
        self.intent_score = {"corrected": len(judged), "agreed": sum(1 for u in judged if self.inferred[u]["intent"] == self.corrections[u])}
        self.budgets = dict((r["category"], r["target"]) for r in conn.execute("SELECT category, target FROM budgets"))
        push = conn.execute("SELECT at, host, rows, marcus_status FROM push_log ORDER BY id DESC LIMIT 1").fetchone()
        self.last_push = dict(push) if push else None
        self.today = date.today()
        self.series = lc.recurring(self.rows, self.today)
        self.flags = lc.flags(self.rows, self.today, self.series, self.reviewed)
        self.refunds = lc.refunds(self.rows, self.today, self.awaiting)
        self.habits = lc.habits(self.rows, self.today)
        self.priorities = lc.priorities(self.rows, self.intents, self.today)
        self.plan = dict((r["lever_id"], r["value"]) for r in conn.execute("SELECT lever_id, value FROM plan"))
        self.cut = lc.levers(self.rows, self.today, self.series, self.habits, self.plan)
        self.timed = []
        self.motive = self._motive(conn)

    def _motive(self, conn):
        """Where and when, joined to the money. Coverage is always stated: a chart built on
        the 43 purchases whose time is known must never read as if it were all 830."""
        by_uid = dict((r.get("uid"), r) for r in self.rows)
        timed, placed, chan = [], [], {}
        undone = {}                     # money that went back was not spent anywhere: one shop read three times what he kept there
        for x in lc.refunds(self.rows, self.today, loose=True)["matched"]:
            undone[x["purchase_uid"]] = undone.get(x["purchase_uid"], 0.0) + x["refunded"]
        for m in conn.execute("SELECT * FROM moments"):
            r = by_uid.get(m["uid"])
            if r is None or r["_k"] != "purchase":          # a row he marked a test charge is not a purchase
                continue
            kept = round(r["amount"] - undone.get(r.get("uid"), 0.0), 2)
            if kept < 0.01:
                continue
            chan[m["channel"]] = chan.get(m["channel"], 0) + 1
            base = {"amount": kept, "merchant": r.get("merchant") or r["_m"], "mkey": r["_m"], "category": r["_cat"], "date": r["date"]}
            if m["ts"] is not None:
                timed.append(dict(base, ts=m["ts"], time_source=m["time_source"]))
            if m["merchant_lat"] is not None:
                placed.append(dict(base, merchant_lat=m["merchant_lat"], merchant_lon=m["merchant_lon"], merchant_place=m["merchant_place"]))
        n = sum(chan.values())
        row = conn.execute("SELECT value, built_at FROM analysis WHERE key='drivers'").fetchone()
        analysis = dict(json.loads(row["value"]), built_at=row["built_at"]) if row else None
        self.timed = timed
        return {"analysis": analysis,
                "coverage": {"purchases": n, "channels": chan, "placed": len(placed), "timed": len(timed),
                             "timed_from": min([t["date"] for t in timed] or [None]),
                             "timed_by": dict((k, sum(1 for t in timed if t["time_source"] == k)) for k in set(t["time_source"] for t in timed))},
                "hour_weekday": motive.hour_weekday(timed), "places": motive.places(placed)[:80]}

    def staleness(self):
        last_import = None
        if self.last_push and self.last_push.get("marcus_status"):
            try:
                last_import = (json.loads(self.last_push["marcus_status"]) or {}).get("last_import")
            except ValueError:
                pass
        return lc.staleness(self.rows, self.today, self.last_push and self.last_push["at"], last_import)


def data(conn):
    with _lock:
        fresh = _cache["built"] == _cache["version"] and _cache.get("day") == date.today()
        if fresh:
            return _cache["data"]
        version = _cache["version"]
    built = Data(conn)
    with _lock:
        _cache.update(data=built, built=version, day=date.today())
    return built


def public_row(r, enrich):
    e = enrich.get(r.get("uid")) or {}
    return {"uid": r.get("uid"), "date": r["date"], "posted": r.get("posted"), "amount": round(r["amount"], 2),
            "merchant": r.get("merchant") or r["_m"], "merchant_key": r["_m"], "description": r.get("description"),
            "category": r["_cat"], "category_by": r.get("_cat_by"), "original_category": r.get("category"), "kind": r.get("kind"),
            "class": r["_k"], "source": r.get("source"), "provisional": r.get("source") == "shortcut",
            "note": e.get("note"), "awaiting_refund": e.get("awaiting_refund"), "intent": e.get("intent")}


def _wake_sender():
    try:        # the sender's own 5-minute tick is too slow for a question about a purchase
        import subprocess
        subprocess.Popen(["launchctl", "kickstart", "gui/%d/com.user.ledger-nudge" % os.getuid()], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except Exception:
        pass


def _make_checkin(conn, tid, epoch, here):
    """Guess what the tap was and queue (or decline) the question. `here` = (lat, lon, age_s) | None."""
    D = data(conn)
    when = datetime.fromtimestamp(epoch)
    purchases = [r for r in D.rows if r["_k"] == "purchase"]
    geo = dict((r["mkey"], (r["lat"], r["lon"])) for r in conn.execute("SELECT mkey, lat, lon FROM merchant_geo WHERE lat IS NOT NULL"))
    approx = set(r["mkey"] for r in conn.execute("SELECT mkey FROM merchant_geo WHERE source = 'city-area'"))
    g = motive.guess_purchase(purchases, [{"ts": t["ts"], "mkey": t["mkey"]} for t in D.timed], set(h["merchant"] for h in D.habits), when, here, geo, approx)
    call, state, text, why = {}, "skipped", None, "nothing to go on"
    if g:
        call = motive.infer_intent({"category": g["category"], "amount": g["typical"], "typical": g["typical"], "channel": "in_person",
                                    "habit": g["habit"], "merchant_count": g["count"], "usual_amount": True, "hour": when.hour})
        if g["p"] >= motive.ASK_BAND[1] and call.get("intent") in ("routine", "need"):
            why = "too sure to be worth asking"
        elif g["p"] < motive.ASK_BAND[0] and len(g["candidates"]) < 2:
            why = "no guess worth asking about"
        else:
            state, why, text = "new", "asking", motive.checkin_text(g, call, when)
    with conn:
        conn.execute("INSERT OR REPLACE INTO checkins(tap_id,epoch,created_at,merchant,mkey,category,intent,confidence,basis,text,state,candidates) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                     (tid, epoch, now_iso(), g and g["merchant"], g and g["mkey"], g and g["category"], call.get("intent"), g and g["p"],
                      json.dumps((g or {}).get("basis") or [why]), text, state, json.dumps((g or {}).get("candidates") or [])))
    return state, why, g and {"merchant": g["merchant"], "p": g["p"], "intent": call.get("intent"), "candidates": [c["merchant"] for c in g["candidates"]]}


_tap_lock = threading.RLock()


def handle_tap(conn, p):
    """One tap (or its location) at a time. The server is threaded and on 09-17 20:37 the Marcus forward and the
    phone's own /here fix landed in the same second: each looked for the other before the other had written, and
    the fix was never attached. Serialised, every order works - the fix is read after the tap is stored, or the
    tap is found after the fix is stored."""
    with _tap_lock:
        return _handle_tap(conn, p)


def _handle_tap(conn, p):
    """Marcus forwards every Wallet tap the instant it arrives, and - when the shortcut sends it - the phone's
    own GPS a few seconds later. Store it; if it opens a new burst (one purchase fires the automation three
    times), guess what it was and queue a check-in. The question waits ~25 s so the location can beat it."""
    try:
        tid, epoch = int(p["id"]), float(p["epoch"])
    except (KeyError, TypeError, ValueError):
        return 400, {"error": "id and epoch required"}
    num = lambda v: float(v) if isinstance(v, (int, float)) and not isinstance(v, bool) else None
    lat, lon, acc = num(p.get("lat")), num(p.get("lon")), num(p.get("acc"))
    here = (lat, lon, 0.0) if lat is not None and lon is not None else None
    if p.get("locate"):
        if not here:
            return 400, {"error": "locate needs lat and lon"}
        with conn:
            conn.execute("UPDATE taps SET lat = ?, lon = ?, acc = ? WHERE id = ?", (lat, lon, acc, tid))
        ck = conn.execute("SELECT state FROM checkins WHERE tap_id = ?", (tid,)).fetchone()
        res = {"ok": True, "located": True}
        if ck and ck["state"] in ("new", "skipped"):          # not asked yet: ask again, knowing where he is
            state, why, g = _make_checkin(conn, tid, epoch, here)
            res.update(checkin=state, why=why, guess=g)
            if state == "new":
                _wake_sender()
        _motive_kick.set()
        return 200, res
    with conn:
        conn.execute("INSERT OR REPLACE INTO taps(id,ts,epoch,ip,blank,amount,merchant,lat,lon,acc) VALUES (?,?,?,?,?,?,?,?,?,?)",
                     (tid, str(p.get("ts") or ""), epoch, p.get("ip"), 1 if p.get("blank") else 0,
                      None if p.get("amount") in (None, "") else str(p["amount"])[:40],
                      None if p.get("merchant") in (None, "") else str(p["merchant"])[:120], lat, lon, acc))
    prev = conn.execute("SELECT MAX(epoch) FROM taps WHERE id != ? AND epoch <= ?", (tid, epoch)).fetchone()[0]
    if (prev is not None and epoch - prev <= 150) or conn.execute("SELECT 1 FROM checkins WHERE tap_id = ?", (tid,)).fetchone():
        return 200, {"ok": True, "checkin": None, "why": "same purchase as the tap before it"}
    if not here:            # the phone's own fix can beat Marcus's forward here by a second or two
        row = conn.execute("SELECT value FROM analysis WHERE key = 'phone_fix'").fetchone()
        fix = json.loads(row["value"]) if row else None
        if fix and abs(epoch - fix["epoch"]) <= 120:
            here = (fix["lat"], fix["lon"], 0.0)
            with conn:
                conn.execute("UPDATE taps SET lat = ?, lon = ?, acc = ? WHERE id = ?", (fix["lat"], fix["lon"], fix.get("acc"), tid))
    state, why, g = _make_checkin(conn, tid, epoch, here or motive.latest_fix(epoch))
    _motive_kick.set()
    if state == "new":
        if here:
            _wake_sender()
        else:
            threading.Timer(25.0, _wake_sender).start()       # give the phone's location a moment to arrive
    return 200, {"ok": True, "checkin": state, "why": why, "guess": g}


def nudge_view(conn, D):
    """What LEDGER would say right now, what is switched on, and what it has already said.
    Computed fresh (not from the cached dataset): the Sunday recap depends on the hour."""
    st = dict((r["kind"], bool(r["enabled"])) for r in conn.execute("SELECT kind, enabled FROM nudge_settings"))
    master = st.get("_master", False)                       # ships OFF: nothing texts the owner until he says so
    sent = dict((r["id"], dict(r)) for r in conn.execute("SELECT * FROM nudge_log"))
    now = datetime.now()
    allv = lc.nudges(D.rows, now, D.series, D.cut, lc.budget_pace(D.rows, D.today, D.budgets) if D.budgets else [], D.flags, D.staleness())
    for n in allv:
        n["enabled"] = st.get(n["kind"], True)
        n["sent"] = n["id"] in sent
    today = now.strftime("%Y-%m-%d")
    return {"ok": True, "master": master, "test_requested": st.get("_test", False),
            "kinds": [{"key": k, "label": lab, "when": when, "enabled": st.get(k, True)} for k, lab, when in lc.NUDGE_KINDS],
            "due": [n for n in allv if master and n["enabled"] and not n["sent"]], "preview": allv,
            "checkins": [dict(r) for r in conn.execute("SELECT * FROM checkins ORDER BY epoch DESC LIMIT 25")],
            "checkin_on": bool(master and st.get("checkin", True)),
            "sent_today": sum(1 for v in sent.values() if (v.get("sent_at") or "")[:10] == today and v.get("kind") not in ("weekly", "test")),
            "log": sorted(sent.values(), key=lambda v: v.get("sent_at") or "", reverse=True)[:12]}


def with_intent(row, D):
    """A ledger row plus what LEDGER thinks the purchase was for, and why."""
    i = D.inferred.get(row["uid"])
    if i:
        row["inferred"] = i
    row["intent_effective"] = D.intents.get(row["uid"])
    return row


def month_view(D, ym):
    """The month's numbers. A past month is judged as of its last day."""
    this = D.today.strftime("%Y-%m")
    if not re.match(r"^\d{4}-\d{2}$", ym or ""):
        ym = this
    start, end = lc.month_bounds(ym)
    as_of = D.today if ym == this else end
    return {"month": ym, "is_current": ym == this,
            "pace": lc.pace(D.rows, as_of, D.series if ym == this else None),
            "categories": lc.by_category(D.rows, start, min(end, as_of)),
            "merchants": lc.merchants(D.rows, start, min(end, as_of))[:40],
            "budgets": lc.budget_pace(D.rows, as_of, D.budgets) if D.budgets else [],
            "intent": dict(lc.intent_summary(D.rows, start, min(end, as_of), D.intents),
                           notable=[dict(with_intent(public_row(r, D.enrich), D))
                                    for r in sorted((r for r in D.rows if start <= r["_d"] <= min(end, as_of) and r["_k"] == "purchase"
                                                     and D.intents.get(r.get("uid")) in ("impulse", "treat", "social")),
                                                    key=lambda r: -r["amount"])[:8]])}


def bundle(D, ym):
    from datetime import timedelta
    out = month_view(D, ym)
    months = sorted(set(r["date"][:7] for r in D.rows))
    out.update({
        "ok": True, "version": VERSION, "today": D.today.isoformat(), "months": months,
        "status": D.staleness(), "trend": lc.category_trend(D.rows),
        "cut": D.cut, "motive": D.motive, "habits": D.habits, "priorities": D.priorities, "recurring": D.series, "upcoming": lc.upcoming(D.series, D.today, D.today + timedelta(days=45)),
        "flags": D.flags, "refunds": D.refunds, "interest": lc.interest_ytd(D.rows, D.today.year),
        "all_time": lc.totals(D.rows),
        "categories_known": sorted(set(r["_cat"] for r in D.rows) | set([lc.TEST_CATEGORY])),
        "budget_targets": D.budgets, "buildable": lc.buildable(D.rows, D.today, D.series),
        "intents": [{"key": k, "label": lab, "hint": hint} for k, lab, hint in lc.INTENTS],
        "intent_score": D.intent_score,
    })
    return out


# ------------------------------------------------------------------- writes
def ingest(conn, p, who):
    txs = p.get("transactions")
    if not isinstance(txs, list):
        return 400, {"error": "transactions must be a list"}
    clean = []
    for t in txs:
        if not isinstance(t, dict) or not t.get("uid") or not re.match(r"^\d{4}-\d{2}-\d{2}", str(t.get("date") or "")):
            return 400, {"error": "every transaction needs uid and date", "bad": str(t)[:120]}
        try:
            amount = float(t.get("amount"))
        except (TypeError, ValueError):
            return 400, {"error": "amount must be a number", "bad": str(t)[:120]}
        clean.append(tuple([str(t["uid"]), str(t["date"])[:10], t.get("posted"), amount] +
                           [t.get(c) for c in TX_COLS[4:]]))
    have = set(r[0] for r in conn.execute("SELECT uid FROM transactions"))
    if not clean and have and not p.get("allow_empty"):
        # a bad read on vr-2 must never be able to blank the mirror
        return 409, {"error": "refusing an empty snapshot over %d rows (send allow_empty to force)" % len(have)}
    new = set(c[0] for c in clean)
    if len(new) != len(clean):
        return 400, {"error": "duplicate uids in snapshot"}
    with conn:
        conn.execute("DELETE FROM transactions")
        conn.executemany("INSERT INTO transactions(%s) VALUES (%s)" % (",".join(TX_COLS), ",".join("?" * len(TX_COLS))), clean)
        conn.execute("INSERT INTO push_log(at,host,who,rows,added,removed,signature,marcus_status) VALUES (?,?,?,?,?,?,?,?)",
                     (now_iso(), str(p.get("host") or "")[:40], who, len(clean), len(new - have), len(have - new),
                      str(p.get("signature") or "")[:120], json.dumps(p.get("marcus_status")) if p.get("marcus_status") else None))
        taps = p.get("taps")
        if isinstance(taps, list):
            # Marcus never sees the phone's GPS (the shortcut sends it straight here), so a snapshot that carries
            # no lat/lon must keep the location LEDGER already attached - the first located tap (09-17 16:39)
            # lost its fix to the very next five-minute push.
            known = dict((r[0], (r[1], r[2], r[3])) for r in conn.execute("SELECT id, lat, lon, acc FROM taps WHERE lat IS NOT NULL"))
            conn.execute("DELETE FROM taps")
            conn.executemany("INSERT OR REPLACE INTO taps(id,ts,epoch,ip,blank,amount,merchant,lat,lon,acc) VALUES (?,?,?,?,?,?,?,?,?,?)",
                             [(t.get("id"), str(t.get("ts") or ""), t.get("epoch"), t.get("ip"), 1 if t.get("blank") else 0,
                               None if t.get("amount") is None else str(t.get("amount"))[:40],
                               None if t.get("merchant") is None else str(t.get("merchant"))[:120])
                              + (known.get(t.get("id"), (None, None, None)) if t.get("lat") is None else (t.get("lat"), t.get("lon"), t.get("acc")))
                              for t in taps if isinstance(t, dict) and t.get("id") is not None])
    _touch()
    _motive_kick.set()
    return 200, {"ok": True, "rows": len(clean), "added": len(new - have), "removed": len(have - new),
                 "taps": len(p["taps"]) if isinstance(p.get("taps"), list) else None}


def set_tx(conn, uid, p):
    if not conn.execute("SELECT 1 FROM transactions WHERE uid=?", (uid,)).fetchone():
        return 404, {"error": "no such transaction"}
    cur = conn.execute("SELECT * FROM enrich WHERE uid=?", (uid,)).fetchone()
    e = dict(cur) if cur else {"uid": uid, "note": None, "category": None, "awaiting_refund": None,
                               "intent": None, "intent_at": None}
    if "note" in p:
        e["note"] = (str(p["note"]).strip()[:500] or None) if p["note"] is not None else None
    if "category" in p:
        e["category"] = (str(p["category"]).strip()[:60] or None) if p["category"] is not None else None
    if "awaiting_refund" in p:
        e["awaiting_refund"] = (e.get("awaiting_refund") or date.today().isoformat()) if p["awaiting_refund"] else None
    if "intent" in p:
        if p["intent"] not in (None, "") and p["intent"] not in lc.INTENT_KEYS:
            return 400, {"error": "intent must be one of " + ", ".join(lc.INTENT_KEYS)}
        e["intent"] = p["intent"] or None
        e["intent_at"] = now_iso() if e["intent"] else None      # WHEN he answered matters: same day beats a week later
    with conn:
        conn.execute("INSERT OR REPLACE INTO enrich(uid,note,category,awaiting_refund,intent,intent_at,updated_at) "
                     "VALUES (?,?,?,?,?,?,?)",
                     (uid, e["note"], e["category"], e["awaiting_refund"], e.get("intent"), e.get("intent_at"), now_iso()))
    _touch()
    return 200, {"ok": True, "enrich": e}


def ask_marcus(question, raw=False):
    """The page's Ask box. Marcus's model does the language and picks a tool; every figure in his answer
    comes back out of LEDGER's own calculators (the spending_* tools), so nothing is estimated.
    auto_memory off: a question about money is not a fact about the owner for Marcus to remember."""
    import urllib.request
    lead = "" if raw else "(Use your spending_* tools for every figure; relay them exactly, and say so if LEDGER reports a caveat.) "
    body = json.dumps({"message": lead + question,
                       "history": [], "persona_id": "default", "auto_memory": False}).encode("utf-8")
    req = urllib.request.Request(MARCUS + "/api/chat", data=body, method="POST", headers={"Content-Type": "application/json"})
    text, loading = "", False
    with urllib.request.urlopen(req, timeout=170) as r:
        for raw in r:
            line = raw.decode("utf-8", "replace").strip()
            if not line.startswith("data: "):
                continue
            try:
                d = json.loads(line[6:])
            except ValueError:
                continue
            if d.get("text"):
                text = d["text"]                  # the stream sends the answer so far, not a delta
            loading = loading or bool(d.get("loading"))
    return {"ok": True, "answer": demojibake(text.strip()), "loading": loading}


def demojibake(s):
    """Marcus's /api/chat stream double-encodes non-ASCII (an em dash arrives as c3 a2 c2 80 c2 94, seen
    2026-09-17). Undo it only when the round trip is lossless - correctly encoded text cannot survive
    .encode('latin-1'), so it falls through untouched and this goes quiet the day Marcus is fixed."""
    try:
        return s.encode("latin-1").decode("utf-8")
    except (UnicodeEncodeError, UnicodeDecodeError):
        return s


def post(conn, path, p, who):
    if path == "/api/ledger/buildable":         # the list is LEDGER's; the judgement is Marcus's, who knows the fleet
        D = data(conn)
        items = lc.buildable(D.rows, D.today, D.series)
        if not items:
            return 200, {"ok": True, "items": [], "answer": "Nothing in the statement looks like software, a service or a subscription."}
        try:
            return 200, dict(ask_marcus(lc.buildable_prompt(items), raw=True), items=items)
        except Exception as e:
            return 502, {"error": "Marcus is not answering (%s)" % type(e).__name__, "items": items}
    if path == "/api/ledger/ask":
        q = str(p.get("q") or "").strip()[:600]
        if not q:
            return 400, {"error": "ask something"}
        try:
            return 200, ask_marcus(q)
        except Exception as e:
            return 502, {"error": "Marcus is not answering (%s) - he may be asleep, restarting, or busy with the GPU" % type(e).__name__}
    if path == "/api/ledger/ingest":
        return ingest(conn, p, who)
    m = re.match(r"^/api/ledger/tx/(.+)$", path)
    if m:
        return set_tx(conn, unquote(m.group(1)), p)
    if path == "/api/ledger/flags/review":
        fid = str(p.get("id") or "")
        if not fid:
            return 400, {"error": "id required"}
        with conn:
            if p.get("reviewed", True):
                conn.execute("INSERT OR REPLACE INTO reviewed(flag_id, at) VALUES (?,?)", (fid, now_iso()))
            else:
                conn.execute("DELETE FROM reviewed WHERE flag_id=?", (fid,))
        _touch()
        return 200, {"ok": True}
    if path == "/api/ledger/alias":
        raw = lc.merchant_key(p.get("raw") or "")
        alias = lc.merchant_key(p.get("alias") or "") if p.get("alias") else ""
        if raw == "UNKNOWN":
            return 400, {"error": "raw merchant required"}
        with conn:
            if alias and alias != raw:
                conn.execute("INSERT OR REPLACE INTO merchant_alias(raw, alias, at) VALUES (?,?,?)", (raw, alias, now_iso()))
            else:
                conn.execute("DELETE FROM merchant_alias WHERE raw=?", (raw,))
        _touch()
        return 200, {"ok": True, "raw": raw, "alias": alias or None}
    if path == "/api/ledger/context":
        days, receipts = p.get("days"), p.get("receipts")
        if not isinstance(days, list) or not isinstance(receipts, list):
            return 400, {"error": "days and receipts must be lists"}
        with conn:
            conn.execute("DELETE FROM days")
            conn.executemany("INSERT OR REPLACE INTO days(date, features) VALUES (?,?)",
                             [(str(d["date"])[:10], json.dumps(dict((k, v) for k, v in d.items() if k != "date" and isinstance(v, (int, float)))))
                              for d in days if isinstance(d, dict) and re.match(r"^\d{4}-\d{2}-\d{2}$", str(d.get("date") or ""))])
            if isinstance(p.get("purchase_context"), list):
                conn.execute("DELETE FROM purchase_context")
                conn.executemany("INSERT OR REPLACE INTO purchase_context(uid, ctx) VALUES (?,?)",
                                 [(str(c["uid"]), json.dumps(dict((k, v) for k, v in c.items() if k != "uid" and isinstance(v, (int, float, bool)))))
                                  for c in p["purchase_context"] if isinstance(c, dict) and c.get("uid")])
            conn.execute("DELETE FROM receipts")
            conn.executemany("INSERT OR REPLACE INTO receipts(uid, ts, matched, domain) VALUES (?,?,?,?)",
                             [(str(r["uid"]), float(r["ts"]), str(r.get("matched") or "")[:30], str(r.get("domain") or "")[:60])
                              for r in receipts if isinstance(r, dict) and r.get("uid") and isinstance(r.get("ts"), (int, float))])
        _motive_kick.set()
        return 200, {"ok": True, "days": len(days), "receipts": len(receipts)}
    if path == "/api/ledger/tap":
        return handle_tap(conn, p)
    if path == "/api/ledger/here":
        # The phone says where it is, straight to LEDGER (tailnet identity - no token in the shortcut). Sent by the
        # "LEDGER here" shortcut as the automation's second step, seconds after the ping went to Marcus.
        def f(v):
            try:
                return float(v)
            except (TypeError, ValueError):
                return None
        lat, lon, acc = f(p.get("lat")), f(p.get("lon")), f(p.get("acc"))
        if lat is None or lon is None or not (-90 <= lat <= 90 and -180 <= lon <= 180):
            return 400, {"error": "lat and lon required"}
        import time as _time
        now = _time.time()
        with conn:
            conn.execute("INSERT OR REPLACE INTO analysis(key, value, built_at) VALUES ('phone_fix', ?, ?)",
                         (json.dumps({"lat": lat, "lon": lon, "acc": acc, "epoch": now}), now_iso()))
        with _tap_lock:         # see handle_tap: the fix and the tap can land in the same second
            ck = conn.execute("SELECT tap_id, epoch FROM checkins WHERE epoch >= ? ORDER BY epoch DESC LIMIT 1", (now - 300,)).fetchone()
            if not ck:
                return 200, {"ok": True, "attached_to": None, "why": "no tap in the last five minutes yet - kept for the next one"}
            code, res = handle_tap(conn, {"id": ck["tap_id"], "epoch": ck["epoch"], "locate": True, "lat": lat, "lon": lon, "acc": acc})
        return code, dict(res, attached_to=ck["tap_id"])
    if path == "/api/ledger/checkins/mark":
        with conn:
            conn.execute("UPDATE checkins SET state = ?, sent_at = COALESCE(?, sent_at) WHERE tap_id = ?",
                         (str(p.get("state") or "")[:20], p.get("sent_at"), p.get("tap_id")))
        return 200, {"ok": True}
    if path == "/api/ledger/checkins/reply":
        verdict, intent = motive.read_reply(p.get("reply"))
        if not verdict:
            return 400, {"error": "empty reply"}
        ck = conn.execute("SELECT mkey, candidates FROM checkins WHERE tap_id = ?", (p.get("tap_id"),)).fetchone()
        if not ck:
            return 404, {"error": "no such check-in"}
        cands, mkey = json.loads(ck["candidates"] or "[]"), None
        if verdict == "void":
            pass
        elif verdict.startswith("choice:"):
            i = int(verdict.split(":")[1]) - 1
            mkey = cands[i]["mkey"] if i < len(cands) else None
            verdict = "confirmed" if i == 0 else "corrected"
        elif verdict == "confirmed":
            mkey = ck["mkey"]
        else:       # "phin cafe in the home town": whichever merchant he has bought from shares the most words with what he said
            said = set(w for w in re.findall(r"[a-z0-9']{3,}", str(p.get("reply")).lower()) if w not in ("the", "was", "and", "not", "for"))
            best = (0, None)
            for k in set(r["_m"] for r in data(conn).rows):
                n = len(said & set(re.findall(r"[a-z0-9']{3,}", k.lower())))
                if n > best[0]:
                    best = (n, k)
            mkey = best[1]
        tap = conn.execute("SELECT lat, lon FROM taps WHERE id = ?", (p.get("tap_id"),)).fetchone()
        if mkey and tap and tap["lat"] is not None:
            # he told us WHAT, the phone told us WHERE: that pins the merchant exactly, and the next guess there is not a guess
            with conn:
                conn.execute("UPDATE merchant_geo SET lat = ?, lon = ?, source = 'tap-confirmed', resolved = 'confirmed by the owner at the till', at = ? "
                             "WHERE mkey = ? AND source IN ('city-area', 'unresolved', 'name')", (tap["lat"], tap["lon"], now_iso(), mkey))
        with conn:
            conn.execute("UPDATE checkins SET reply = ?, reply_at = ?, verdict = ?, reply_intent = ?, reply_mkey = ?, state = 'answered' WHERE tap_id = ?",
                         (str(p.get("reply"))[:200], p.get("reply_at") or now_iso(), verdict, intent, mkey, p.get("tap_id")))
        _motive_kick.set()
        return 200, {"ok": True, "verdict": verdict, "intent": intent, "merchant": mkey}
    if path == "/api/ledger/nudges/settings":
        kind = str(p.get("kind") or "")
        if kind not in lc.NUDGE_KEYS + ("_master", "_test"):
            return 400, {"error": "unknown kind"}
        with conn:
            conn.execute("INSERT OR REPLACE INTO nudge_settings(kind, enabled) VALUES (?,?)", (kind, 1 if p.get("enabled") else 0))
        return 200, {"ok": True}
    if path == "/api/ledger/nudges/sent":               # the sender reports what it delivered, so nothing is said twice
        nid = str(p.get("id") or "")[:200]
        if not nid:
            return 400, {"error": "id required"}
        with conn:
            conn.execute("INSERT OR REPLACE INTO nudge_log(id, kind, text, sent_at, state) VALUES (?,?,?,?,?)",
                         (nid, str(p.get("kind") or "")[:20], str(p.get("text") or "")[:600], now_iso(), str(p.get("state") or "ok")[:20]))
            if p.get("kind") == "test":
                conn.execute("INSERT OR REPLACE INTO nudge_settings(kind, enabled) VALUES ('_test', 0)")
        return 200, {"ok": True}
    if path == "/api/ledger/plan":
        lid = str(p.get("id") or "")[:200]
        if not re.match(r"^(habit|sub|cat):.+", lid):
            return 400, {"error": "id must be a lever id"}
        with conn:
            if p.get("value") is None:
                conn.execute("DELETE FROM plan WHERE lever_id=?", (lid,))
            else:
                try:
                    v = max(0.0, float(p["value"]))
                except (TypeError, ValueError):
                    return 400, {"error": "value must be a number, or null to clear"}
                conn.execute("INSERT OR REPLACE INTO plan(lever_id, value, at) VALUES (?,?,?)", (lid, v, now_iso()))
        _touch()
        return 200, {"ok": True}
    if path == "/api/ledger/budgets":
        cat = str(p.get("category") or "").strip()[:60]
        if not cat:
            return 400, {"error": "category required"}
        try:
            target = float(p.get("target") or 0)
        except (TypeError, ValueError):
            return 400, {"error": "target must be a number"}
        with conn:
            if target > 0:
                conn.execute("INSERT OR REPLACE INTO budgets(category, target, goal_item, at) VALUES (?,?,?,?)",
                             (cat, target, p.get("goal_item"), now_iso()))
            else:
                conn.execute("DELETE FROM budgets WHERE category=?", (cat,))
        _touch()
        return 200, {"ok": True}
    return None


# --------------------------------------------------------------------- http
DENIED = ("<!doctype html><meta charset=utf-8><title>LEDGER</title>"
          "<body style='font:16px system-ui;margin:3rem;max-width:34rem'>"
          "<h1 style='font-size:1rem;letter-spacing:.2em'>LEDGER</h1>"
          "<p>This surface answers only to the owner's own tailnet devices.</p>"
          "<p style='color:#777'>Seen as: %s</p>")


class H(BaseHTTPRequestHandler):
    server_version = "ledger/" + VERSION

    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="application/json; charset=utf-8", cors=False):
        if isinstance(body, (dict, list)):
            body = json.dumps(body, ensure_ascii=False)
        data_ = body.encode("utf-8") if isinstance(body, str) else body
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data_)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        if cors:        # only the lamp route, only for the hub shell, and it carries no amounts
            self.send_header("Access-Control-Allow-Origin", SHELL_ORIGIN)
            self.send_header("Vary", "Origin")
        self.end_headers()
        self.wfile.write(data_)

    # ---- identity
    def _proxied(self):
        return any(self.headers.get(h) is not None
                   for h in ("X-Forwarded-For", "X-Forwarded-Host", "X-Forwarded-Proto"))

    def _who(self):
        login = (self.headers.get("Tailscale-User-Login") or "").strip().lower()
        if self._proxied():
            return login or None            # through the proxy: only a tailnet identity counts
        if self.client_address[0] in ("127.0.0.1", "::1"):
            return "local"                  # never proxied: a process on this Mac
        return None

    def _owner(self):
        return self._who() in ("local", OWNER)

    def _same_origin(self):
        """Writes from a browser must come from LEDGER's own page. Non-browser
        callers (the vr-2 pusher, the sweep) send no Origin and pass."""
        origin = self.headers.get("Origin")
        if not origin:
            return True
        host = (self.headers.get("X-Forwarded-Host") or self.headers.get("Host") or "").lower()
        return urlparse(origin).netloc.lower() == host

    def _whoami(self):
        return {"who": self._who(), "owner": self._owner(), "proxied": self._proxied(),
                "peer": self.client_address[0],
                "headers": dict((k, v) for k, v in self.headers.items()
                                if k.lower().startswith(("tailscale-", "x-forwarded-")) or k.lower() in ("host", "origin"))}

    def do_OPTIONS(self):
        self.send_response(204)
        if urlparse(self.path).path.rstrip("/") == "/api/ledger/status":
            self.send_header("Access-Control-Allow-Origin", SHELL_ORIGIN)
            self.send_header("Access-Control-Allow-Methods", "GET, OPTIONS")
            self.send_header("Access-Control-Max-Age", "600")
        self.end_headers()

    def do_GET(self):
        u = urlparse(self.path)
        path = u.path.rstrip("/") or "/"
        q = dict((k, v[0]) for k, v in parse_qs(u.query).items())
        try:
            if path == "/healthz":
                return self._send(200, {"ok": True, "version": VERSION})
            if path == "/whoami":
                return self._send(200, self._whoami())
            if not self._owner():
                if path.startswith("/api/"):
                    return self._send(401, {"error": "not one of the owner's tailnet devices", "who": self._who()},
                                      cors=(path == "/api/ledger/status"))
                return self._send(401, DENIED % (self._who() or "unidentified"), "text/html; charset=utf-8")
            if path in ("/", "/index.html", "/ledger.html"):
                try:
                    return self._send(200, (HERE / "ledger.html").read_bytes(), "text/html; charset=utf-8")
                except OSError:
                    return self._send(404, {"error": "missing ledger.html"})
            conn = _db()
            try:
                D = data(conn)
                if path == "/api/ledger/status":
                    st = D.staleness()
                    waiting = sum(1 for f in D.flags if not f["reviewed"])
                    return self._send(200, {"ok": True, "rows": st["rows"], "through": st["through"],
                                            "stale": st["stale"], "stale_days": st["stale_days"],
                                            "unreviewed_flags": waiting, "lamp": bool(st["rows"]) and (st["stale"] or waiting > 0),
                                            "last_push": st["last_push"]}, cors=True)
                if path == "/api/ledger/all":
                    return self._send(200, bundle(D, q.get("month")))
                if path == "/api/ledger/summary":
                    out = month_view(D, q.get("month"))
                    out.update(ok=True, status=D.staleness(), interest=lc.interest_ytd(D.rows, D.today.year))
                    return self._send(200, out)
                if path == "/api/ledger/recurring":
                    from datetime import timedelta
                    return self._send(200, {"ok": True, "recurring": D.series,
                                            "upcoming": lc.upcoming(D.series, D.today, D.today + timedelta(days=45))})
                if path == "/api/ledger/flags":
                    return self._send(200, {"ok": True, "flags": D.flags})
                if path == "/api/ledger/refunds":
                    return self._send(200, dict(D.refunds, ok=True))
                if path == "/api/ledger/candidates":
                    return self._send(200, {"ok": True, "candidates": lc.candidates(D.series, D.flags, D.refunds, D.staleness(), D.cut)})
                if path == "/api/ledger/say/summary":
                    return self._send(200, lc.say_summary(D.rows, D.today, q.get("period"), D.series), "text/plain; charset=utf-8")
                if path == "/api/ledger/say/search":
                    notes = dict((u, e.get("note")) for u, e in D.enrich.items() if e.get("note"))
                    return self._send(200, lc.say_search(D.rows, D.today, q.get("q"), q.get("days"), notes), "text/plain; charset=utf-8")
                if path == "/api/ledger/say/whatif":
                    return self._send(200, lc.say_whatif(D.rows, D.today, D.series, q.get("target"), q.get("change")), "text/plain; charset=utf-8")
                if path == "/api/ledger/say/pattern":
                    return self._send(200, lc.say_pattern(D.rows, D.today, D.timed, q.get("weekday"), q.get("hour")), "text/plain; charset=utf-8")
                if path == "/api/ledger/say/recurring":
                    return self._send(200, lc.say_recurring(D.series, D.rows, D.today, D.habits), "text/plain; charset=utf-8")
                if path == "/api/ledger/say/plan":            # Marcus: spending_plan - the cut-spending plan, read out
                    return self._send(200, lc.say_plan(D.cut, D.rows, D.today), "text/plain; charset=utf-8")
                if path == "/api/ledger/say/buildable":       # Marcus: spending_buildable - the build-instead-of-buy list
                    return self._send(200, lc.say_buildable(lc.buildable(D.rows, D.today, D.series), D.rows, D.today), "text/plain; charset=utf-8")
                if path == "/api/ledger/nudges":
                    return self._send(200, nudge_view(conn, D))
                if path == "/api/ledger/moments":          # vr-2 asks this, to build the hour-around-the-buy context beside the raw stores
                    return self._send(200, {"ok": True, "moments": dict((r["uid"], r["ts"]) for r in conn.execute("SELECT uid, ts FROM moments WHERE ts IS NOT NULL"))})
                if path == "/api/ledger/taps":
                    rows_ = [dict(r) for r in conn.execute("SELECT * FROM taps ORDER BY epoch DESC LIMIT 500")]
                    return self._send(200, {"ok": True, "count": conn.execute("SELECT COUNT(*) FROM taps").fetchone()[0], "taps": rows_})
                if path == "/api/ledger/brief":
                    return self._send(200, lc.brief(D.rows, D.today), "text/plain; charset=utf-8")
                if path == "/api/ledger/transactions":
                    rows = D.rows
                    if q.get("since"):
                        rows = [r for r in rows if r["date"] >= q["since"][:10]]
                    if q.get("until"):
                        rows = [r for r in rows if r["date"] <= q["until"][:10]]
                    if q.get("category"):
                        rows = [r for r in rows if r["_cat"] == q["category"]]
                    if q.get("merchant"):
                        rows = [r for r in rows if r["_m"] == q["merchant"]]
                    if q.get("class"):
                        rows = [r for r in rows if r["_k"] == q["class"]]
                    if q.get("intent") == "none":
                        rows = [r for r in rows if r["_k"] == "purchase" and r.get("uid") not in D.intents]
                    elif q.get("intent"):
                        rows = [r for r in rows if D.intents.get(r.get("uid")) == q["intent"]]
                    if q.get("q"):
                        needle = q["q"].lower()
                        rows = [r for r in rows if needle in " ".join(
                            str(x or "") for x in (r.get("merchant"), r.get("description"), r["_cat"],
                                                   (D.enrich.get(r.get("uid")) or {}).get("note"))).lower()]
                    total = len(rows)
                    limit = max(1, min(1000, int(q.get("limit") or 200)))
                    offset = max(0, int(q.get("offset") or 0))
                    page = list(reversed(rows))[offset:offset + limit]
                    return self._send(200, {"ok": True, "total": total, "sum": lc.totals(rows),
                                            "transactions": [with_intent(public_row(r, D.enrich), D) for r in page]})
            finally:
                conn.close()
            return self._send(404, {"error": "no such route"})
        except Exception as e:                     # never leak a traceback to a client
            sys.stderr.write("GET %s failed: %r\n" % (path, e))
            return self._send(500, {"error": "internal error"})

    def do_POST(self):
        path = urlparse(self.path).path.rstrip("/")
        try:
            if not self._owner():
                return self._send(401, {"error": "not one of the owner's tailnet devices", "who": self._who()})
            if not self._same_origin():
                return self._send(403, {"error": "cross-origin write refused"})
            if "application/json" not in (self.headers.get("Content-Type") or "").lower():
                return self._send(415, {"error": "application/json required"})
            n = int(self.headers.get("Content-Length") or 0)
            if n > 20 * 1024 * 1024:
                return self._send(413, {"error": "too large"})
            try:
                p = json.loads(self.rfile.read(n).decode("utf-8") or "{}")
            except ValueError:
                return self._send(400, {"error": "bad json"})
            if not isinstance(p, dict):
                return self._send(400, {"error": "object required"})
            conn = _db()
            try:
                res = post(conn, path, p, self._who())
            finally:
                conn.close()
            if res is None:
                return self._send(404, {"error": "no such route"})
            return self._send(res[0], res[1])
        except Exception as e:
            sys.stderr.write("POST %s failed: %r\n" % (path, e))
            return self._send(500, {"error": "internal error"})


if __name__ == "__main__":
    init_db()
    print("ledger %s on %s:%d db=%s owner=%s" % (VERSION, BIND, PORT, DB, OWNER), flush=True)
    if os.environ.get("LEDGER_MOTIVE", "1") != "0":
        threading.Thread(target=_motive_loop, daemon=True).start()
    ThreadingHTTPServer((BIND, PORT), H).serve_forever()
