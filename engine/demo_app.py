#!/usr/bin/env python3
"""LEDGER demo engine: the real server, no network, no fleet.

The public demo (https://producer456hub.github.io/ledger-demo/) runs the UNMODIFIED server.py inside the
visitor's browser under Pyodide. Every request the page would have sent over HTTP is handed to the server's
own request handler through a fake socket, so the demo behaves exactly like the live instance: same
calculators, same writes, same JSON - on a database of invented transactions that lives only in that tab.

What is different, and only here:
  - Ask / "which could I build" never reach Marcus (a language model on the owner's network). The question
    is routed straight to LEDGER's own calculators (`say_*`) - the same functions Marcus's tools call.
  - The clock is frozen at the day the demo was built (engine/demo_meta.json), so the invented year stays
    "current" no matter when someone opens the page.
  - WAL is off (the in-browser file system has no shared memory) and nothing tries to wake a launchd job.

This file also runs under plain CPython - `python3 -m unittest demo.test_demo` exercises it - so the
browser is never the first place a bug shows up.
"""
import io
import json
import os
import re
import sys
from datetime import date

HERE = os.path.dirname(os.path.abspath(__file__))
os.environ.setdefault("LEDGER_DB", os.path.join(HERE, "ledger.db"))
os.environ["LEDGER_MOTIVE"] = "0"                          # no background analysis thread
os.environ["POLARIS_DIR"] = os.path.join(HERE, "no-such-dir")  # never a real Mapblock store
os.environ["LEDGER_MARCUS"] = "http://127.0.0.1:9"        # never reached: ask_marcus is replaced below
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import server  # noqa: E402
import ledger_core as lc  # noqa: E402

server.SCHEMA = server.SCHEMA.replace("PRAGMA journal_mode=WAL;", "")
server._wake_sender = lambda: None
server.H.log_message = lambda *a, **k: None

_meta_path = os.path.join(HERE, "demo_meta.json")
if os.path.exists(_meta_path):
    with open(_meta_path, encoding="utf-8") as _f:
        _frozen = date.fromisoformat(json.load(_f)["today"])

    class _FrozenDate(date):
        @classmethod
        def today(cls):
            return _frozen
    server.date = _FrozenDate


# ------------------------------------------------------------------ Ask, without a model
_DAYS = r"\b(monday|tuesday|wednesday|thursday|friday|saturday|sunday|mon|tue|tues|wed|thu|thur|thurs|fri|sat|sun)s?\b"
_HOURS = {"morning": 9, "breakfast": 8, "lunch": 12, "noon": 12, "midday": 12, "afternoon": 15, "evening": 19,
          "dinner": 19, "night": 21, "late": 22}


def _hour(ql):
    m = re.search(r"\b(\d{1,2})\s*(am|pm)\b", ql)
    if m:
        return (int(m.group(1)) % 12 + (12 if m.group(2) == "pm" else 0)) % 24
    m = re.search(r"\b(\d{1,2}):\d{2}\b", ql)
    if m:
        return int(m.group(1)) % 24
    for word, h in _HOURS.items():
        if re.search(r"\b%s\b" % word, ql):
            return h
    return None


def ask_demo(question, raw=False):
    """Route a plain-words question to the calculator Marcus's tool would have called. Every figure is
    LEDGER's; only the language model is missing, and the answer says so nowhere - the numbers speak."""
    q = (question or "").strip()
    ql = q.lower()
    conn = server._db()
    try:
        D = server.data(conn)
        notes = dict((u, e.get("note")) for u, e in D.enrich.items() if e.get("note"))
    finally:
        conn.close()
    rows, today = D.rows, D.today
    if raw:                                                  # the "build instead of buy" list
        items = lc.buildable(rows, today, D.series)
        lines = ["In the real thing this list goes to a local language model that knows what the owner has "
                 "already built, and it says which of these a weekend of code could actually replace. "
                 "The demo has no model, so here is the arithmetic on its own.", "",
                 "| What | Kind | A year |", "|---|---|---|"]
        lines += ["| %s | %s | %s |" % (i["merchant"], i["category"], lc.money(i["yearly"])) for i in items]
        lines += ["", "**Together: %s a year.**" % lc.money(sum(i["yearly"] for i in items))]
        return {"ok": True, "answer": "\n".join(lines), "loading": False}
    if not q:
        ans = "Ask something - a merchant, a category, a what-if, a weekday."
    elif re.search(r"what if|\bstop|\bquit|\bcut (back|down|out|my|the|spending on)|cancel|halv|\bhalf\b|instead of (going|paying)|fewer|\bless\b|one fewer", ql):
        target = re.sub(r"^.*?\b(if i|i)\s+(stopped|stop|quit|cut( back on| down on| spending on| out)?|cancell?ed|cancel|halved|halve|gave up|give up|dropped|drop)\s*", "", ql)
        target = re.sub(r"\?+$", "", target).strip() or ql
        ans = lc.say_whatif(rows, today, D.series, target, change=ql)      # a what-if wins over the plan reading: "what if I cut spending on coffee?"
    elif re.search(r"\bplan\b|\blevers?\b|\bchosen\b|where could the money come|where can i save", ql):
        ans = lc.say_plan(D.cut, rows, today)                # what Marcus's spending_plan tool reads
    elif re.search(r"\b(could|can|should|would) i build\b|\bbuild (it )?myself\b|\bbuild instead\b|\binstead of buy|software (do )?i pay|replace .*with (code|software)", ql):
        ans = lc.say_buildable(lc.buildable(rows, today, D.series), rows, today)     # spending_buildable; a merchant called Build-A-Bear still goes to search
    elif re.search(r"subscri|recurring|repeat|paying for|\bbills?\b|memberships?", ql):
        ans = lc.say_recurring(D.series, rows, today, D.habits)
    elif re.search(_DAYS, ql) or re.search(r"weekend|\d\s*(am|pm)\b|morning|afternoon|evening|night", ql):
        m = re.search(_DAYS, ql)
        wd = next((w for w in lc.WEEKDAYS if w.startswith(m.group(1)[:3])), None) if m else None
        hr = _hour(ql)
        if wd is None and "weekend" in ql:
            ans = lc.say_pattern(rows, today, D.timed, "saturday", hr) + "\n\n" + lc.say_pattern(rows, today, D.timed, "sunday", hr)
        else:
            ans = lc.say_pattern(rows, today, D.timed, wd, hr)
    elif re.search(r"compare|last month|\bvs\b|versus|than last|month before", ql):
        ans = lc.say_summary(rows, today, "this_month", D.series) + "\n\n" + lc.say_summary(rows, today, "last_month", D.series)
    elif re.search(r"this year|\bytd\b|year so far|so far this year", ql):
        ans = lc.say_summary(rows, today, "year", D.series)
    elif re.search(r"this week|last 7|past week|seven days", ql):
        ans = lc.say_summary(rows, today, "week", D.series)
    else:
        sel, label = lc._select(rows, q)
        if sel:
            ans = lc.say_search(rows, today, label or q, 90, notes)
        elif re.search(r"today", ql):
            ans = lc.say_summary(rows, today, "today", D.series)
        elif re.search(r"yesterday", ql):
            ans = lc.say_summary(rows, today, "yesterday", D.series)
        else:
            ans = lc.say_summary(rows, today, "this_month", D.series)
    return {"ok": True, "answer": ans, "loading": False}


server.ask_marcus = ask_demo


# ------------------------------------------------------------------ one request, no socket
class _Sock:
    """What http.server needs from a socket: a readable file of the request, and sendall() for the reply."""

    def __init__(self, data):
        self.data, self.out = data, io.BytesIO()

    def makefile(self, mode, *a, **k):
        return io.BytesIO(self.data)

    def sendall(self, b):
        self.out.write(b)

    def fileno(self):
        return -1


def dispatch(method, target, body=None):
    """(method, path?query, JSON body or None) -> {"status", "type", "body"} - exactly what the live server
    would have answered a local, same-origin caller."""
    data = b""
    if body is not None:
        data = (body if isinstance(body, str) else json.dumps(body)).encode("utf-8")
    head = "%s %s HTTP/1.0\r\nHost: demo\r\n" % (method, target)
    if data or method == "POST":
        head += "Content-Type: application/json\r\nContent-Length: %d\r\n" % len(data)
    sock = _Sock(head.encode("utf-8") + b"\r\n" + data)
    server.H(sock, ("127.0.0.1", 40000), None)
    raw = sock.out.getvalue()
    hdr, _, payload = raw.partition(b"\r\n\r\n")
    lines = hdr.decode("latin-1").split("\r\n")
    status = int(lines[0].split()[1]) if lines and len(lines[0].split()) > 1 else 500
    headers = dict((k.strip().lower(), v.strip()) for k, v in (l.split(":", 1) for l in lines[1:] if ":" in l))
    return {"status": status, "type": headers.get("content-type", "application/json; charset=utf-8"),
            "body": payload.decode("utf-8", "replace")}


def init():
    server.init_db()


init()
