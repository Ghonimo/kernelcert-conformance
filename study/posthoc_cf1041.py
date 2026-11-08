#!/usr/bin/env python3
"""Post hoc (after the counted run): Certifaiger 10.4.1 (commit b540f0c5, released on
2026-11-05, after the counted run), release build, on every pair of the counted run, under
the counted run's caps and with the harness's own call and classification
(run_pairs.certifaiger). Compares each outcome with the counted outcome of 10.4.0's release
build (column cf of results.csv and results_fixed.csv).
    posthoc_cf1041.py COUNTED_DIR FIXED_DIR TOOLS_DIR OUT.csv [--jobs N]
COUNTED_DIR holds results.csv, results_fixed.csv and corpus/; FIXED_DIR is
study/corpus/fixed; TOOLS_DIR holds certifaiger-10.4.1 (study/tools/setup_linux.sh).
Raw outputs go to posthoc_cf1041_logs/ beside OUT.csv.
(run on the study host, 2026-11-07; results/posthoc_cf1041.csv)"""
import csv
import os
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from run_pairs import certifaiger  # noqa: E402  same call, caps and classification

counted, fixed, tools, out = [os.path.abspath(x) for x in sys.argv[1:5]]
jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 8
tool = os.path.join(tools, "certifaiger-10.4.1", "bin", "check")
assert os.access(tool, os.X_OK), tool
logs = os.path.join(os.path.dirname(out), "posthoc_cf1041_logs")
os.makedirs(logs, exist_ok=True)
items = [(os.path.join(counted, "corpus"), r)
         for r in csv.DictReader(open(os.path.join(counted, "results.csv")))]
items += [(fixed, r) for r in csv.DictReader(open(os.path.join(counted, "results_fixed.csv")))]
ids = [r["id"] for _, r in items]
assert len(set(ids)) == len(ids), "pair ids are not unique"


def one(item):
    corpus, r = item
    info, log = certifaiger(tool, os.path.join(corpus, r["model"]), os.path.join(corpus, r["witness"]))
    with open(os.path.join(logs, r["id"] + ".log"), "w") as f:
        f.write(log)
    same_v = info["v"] == r["cf"]
    same_reason = same_v and info["failed"] == r["cf_failed"] and str(info["strat"]) == str(r["cf_strat"])
    return [r["id"], r["family"], r["cf"], r["cf_failed"], r["cf_strat"],
            info["v"], info["failed"], info["strat"], info["rc"], info["t"], int(same_v), int(same_reason)]


with ThreadPoolExecutor(max_workers=jobs) as ex:
    res = list(ex.map(one, items))
with open(out, "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["id", "family", "cf", "cf_failed", "cf_strat", "new", "new_failed", "new_strat",
                "new_rc", "new_t", "same_verdict", "same_reason"])
    w.writerows(res)
print("pairs:", len(res), "same verdict:", sum(r[10] for r in res),
      "same verdict and reason:", sum(r[11] for r in res))
for (a, b), n in sorted(Counter((r[2], r[5]) for r in res if not r[10]).items()):
    print("  10.4.0 %s -> 10.4.1 %s: %d" % (a, b, n))
