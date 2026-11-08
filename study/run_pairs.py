#!/usr/bin/env python3
"""Runs every checker on every pair of a corpus manifest (on the Linux host).

    run_pairs.py CORPUS_DIR TOOLS_DIR REPO_DIR OUT.csv [--jobs N] [--limit K]

Per pair (row of CORPUS_DIR/manifest.csv):
  gt        ground truth on the model: bfs.py (safe / unsafe / error)
  kc        reference checker: checker/front.py, then tools/bin/kcheck
            (accept / reject / refused:<reason> / error); per-check entries kept
  kcdiag    kcheck --diag (Certifaiger's form of Transition and the D1 variant), run only
            when kc accepts and Certifaiger current rejects
  cf, ca, co Certifaiger current (release), current with assertions, 10.2.1
            (accept / reject / error); the failing checks it names, and whether it said
            "not stratified"
  va        Valaig's verified checker (accept / reject / error)
Raw outputs go to OUT.csv's directory under logs/<id>/.
"""
import csv
import json
import os
import re
import resource
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

TIMEOUT = 300


def _raise_as():
    """Lean executables reserve much address space per thread; lift the soft cap on
    virtual memory to the hard one in each child."""
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (hard, hard))


def run(cmd, timeout=TIMEOUT, cwd=None):
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, cwd=cwd,
                           preexec_fn=_raise_as)
        return p.returncode, p.stdout + p.stderr, time.time() - t0
    except subprocess.TimeoutExpired:
        return 124, "TIMEOUT", time.time() - t0


# Certifaiger's own `limit` wrapper (runlim) reads TIME (seconds) and SPACE (MB). On
# witnesses whose gates are numbered out of order its release builds grew to 7-12 GB
# per process; the caps keep the shared host safe (DEVIATIONS.md, D1).
CF_TIME, CF_SPACE = "120", "4096"


def certifaiger(tool, model, witness):
    env = dict(os.environ, TIME=CF_TIME, SPACE=CF_SPACE)
    t0 = time.time()
    try:
        p = subprocess.run([tool, model, witness], capture_output=True, text=True,
                           timeout=TIMEOUT, env=env, preexec_fn=_raise_as)
        rc, out = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        rc, out = 124, "TIMEOUT"
    dt = time.time() - t0
    failed = sorted(set(re.findall(r"Error: (\w+) check failed", out)))
    strat = "not stratified" in out
    limit = "out of memory" in out or "space limit" in out.lower() or \
        "out of time" in out or "time limit" in out.lower()
    if rc == 0 and "valid witness" in out:
        v = "accept"
    elif rc == 124:
        v = "timeout"
    elif limit and not failed:
        v = "limit"
    elif failed or strat:
        v = "reject"
    elif rc in (134, 139) or "Assertion" in out or "assert" in out.lower():
        v = "crash"
    else:
        v = "error"
    return {"v": v, "failed": "+".join(failed), "strat": int(strat), "rc": rc, "t": round(dt, 3)}, out


def main(argv):
    corpus, tools, repo, out_csv = [os.path.abspath(x) for x in argv[:4]]
    jobs = int(argv[argv.index("--jobs") + 1]) if "--jobs" in argv else 8
    limit = int(argv[argv.index("--limit") + 1]) if "--limit" in argv else None
    rows = list(csv.DictReader(open(os.path.join(corpus, "manifest.csv"))))
    if limit:
        rows = rows[:limit]
    logs = os.path.join(os.path.dirname(out_csv), "logs")
    os.makedirs(logs, exist_ok=True)
    front = os.path.join(repo, "checker", "front.py")
    bfs = os.path.join(repo, "study", "tools", "bfs.py")
    kcheck = os.path.join(tools, "bin", "kcheck")
    valaig = os.path.join(tools, "bin", "valaigcert")
    cert = {k: os.path.join(tools, d, "bin", "check") for k, d in
            (("cf", "certifaiger-current"), ("ca", "certifaiger-current-assert"),
             ("co", "certifaiger-10.2.1"))}
    gt_cache = {}

    def gt_of(model):
        if model not in gt_cache:
            rc, out, dt = run([sys.executable, "-I", bfs, model])
            word = out.split()[0] if out.split() else "error"
            gt_cache[model] = (word if word in ("safe", "unsafe") else "error",
                               out.strip().split()[1] if word == "unsafe" and len(out.split()) > 1 else "")
        return gt_cache[model]

    def one(r):
        m = os.path.join(corpus, r["model"])
        w = os.path.join(corpus, r["witness"])
        d = os.path.join(logs, r["id"])
        os.makedirs(d, exist_ok=True)
        res = dict(r)
        res["gt"], res["gt_depth"] = gt_of(m)
        # reference checker
        rc, out, dt = run([sys.executable, "-I", front, m, w])
        kc = {}
        if rc == 0:
            jf = os.path.join(d, "kc.json")
            with open(jf, "w") as f:
                f.write(out)
            rc2, out2, dt2 = run([kcheck, jf])
            dt += dt2
            try:
                kc = json.loads(out2.strip().splitlines()[-1])
            except (ValueError, IndexError):
                kc = {"verdict": "error"}
            res["kc"] = kc.get("verdict", "error")
            if res["kc"] == "refused":
                res["kc"] = "refused:" + kc.get("reason", "")
        else:
            try:
                kc = json.loads(out.strip().splitlines()[-1])
                res["kc"] = "refused:" + kc.get("reason", "")
            except (ValueError, IndexError):
                res["kc"] = "error"
        for k in ("strat", "reset", "trans", "prop", "base", "step"):
            res["kc_" + k] = int(bool(kc.get(k))) if k in kc else ""
        res["kc_t"] = round(dt, 3)
        # Certifaiger, three builds
        for k, tool in cert.items():
            info, log = certifaiger(tool, m, w)
            with open(os.path.join(d, k + ".log"), "w") as f:
                f.write(log)
            for f_, v in info.items():
                res["%s_%s" % (k, f_)] = v
            res[k] = info["v"]
        # attribution, only where the reference checker accepts and Certifaiger rejects
        res["kc_transCF"] = res["kc_transD1"] = ""
        if res["kc"] == "accept" and res["cf"] == "reject":
            rc3, out3, _ = run([kcheck, os.path.join(d, "kc.json"), "--diag"], timeout=1800)
            try:
                dg = json.loads(out3.strip().splitlines()[-1])
                res["kc_transCF"] = int(bool(dg.get("transCF")))
                res["kc_transD1"] = int(bool(dg.get("transD1")))
            except (ValueError, IndexError):
                res["kc_transCF"] = res["kc_transD1"] = "error"
        # Valaig
        if os.path.exists(valaig):
            # Valaig calls an external `cadical`; tools/bin holds one built from the
            # sources Certifaiger vendors.
            rc4, out4, dt4 = run(["env", "PATH=%s:%s" % (os.path.join(tools, "bin"), os.environ.get("PATH", "")),
                                  valaig, m, w])
            with open(os.path.join(d, "va.log"), "w") as f:
                f.write(out4)
            res["va"] = "accept" if "CERTIFICATE SAFE" in out4 else ("timeout" if rc4 == 124 else "reject_or_error")
            res["va_rc"] = rc4
        else:
            res["va"] = "absent"
            res["va_rc"] = ""
        return res

    t0 = time.time()
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        results = list(ex.map(one, rows))
    keys = list(results[0].keys()) if results else []
    for r in results:
        for k in r:
            if k not in keys:
                keys.append(k)
    with open(out_csv, "w", newline="") as f:
        wr = csv.DictWriter(f, fieldnames=keys)
        wr.writeheader()
        for r in results:
            wr.writerow(r)
    print("%d pairs in %.0f s -> %s" % (len(results), time.time() - t0, out_csv))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
