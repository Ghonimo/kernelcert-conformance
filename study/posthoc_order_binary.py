#!/usr/bin/env python3
"""Post hoc (after the counted run): each `order` witness converted to binary AIGER with
aigtoaig, which orders the gates, and checked again by Certifaiger 10.4.0 (release) under
the same caps. Compares the verdict with the ordered original's counted verdict.
    posthoc_order_binary.py COUNTED_DIR TOOLS_DIR OUT.csv
(run on the study host, 2026-11-04, after the counted run; results/posthoc_order_binary.csv)"""
import csv, os, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
counted, tools, out = sys.argv[1:4]
rows = {r["id"]: r for r in csv.DictReader(open(os.path.join(counted, "results.csv")))}
man = {r["id"]: r for r in csv.DictReader(open(os.path.join(counted, "corpus", "manifest.csv")))}
order = [r for r in rows.values() if r["family"] == "order"]
aigtoaig = os.path.join(tools, "certifaiger-current", "bin", "aigtoaig")
check = os.path.join(tools, "certifaiger-current", "bin", "check")
tmp = tempfile.mkdtemp(prefix="posthoc_", dir=os.path.dirname(os.path.abspath(out)))
def one(r):
    m = os.path.join(counted, "corpus", r["model"]); w = os.path.join(counted, "corpus", r["witness"])
    b = os.path.join(tmp, r["id"] + ".aig")
    c = subprocess.run([aigtoaig, w, b], capture_output=True, text=True)
    if c.returncode != 0:
        return r["id"], "aigtoaig-failed", rows[man[r["id"]]["base"]]["cf"]
    env = dict(os.environ, TIME="120", SPACE="4096")
    p = subprocess.run([check, m, b], capture_output=True, text=True, env=env, timeout=300)
    o = p.stdout + p.stderr
    v = "accept" if p.returncode == 0 and "valid witness" in o else ("reject" if ("check failed" in o or "not stratified" in o) else "other:%d" % p.returncode)
    return r["id"], v, rows[man[r["id"]]["base"]]["cf"]
with ThreadPoolExecutor(max_workers=12) as ex:
    res = list(ex.map(one, order))
with open(out, "w") as f:
    f.write("id,binary_verdict,ordered_verdict\n")
    for t in res: f.write(",".join(t) + "\n")
same = sum(1 for _, v, b in res if v == b)
print("order witnesses:", len(res), "binary verdict equals ordered verdict:", same)
