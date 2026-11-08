#!/usr/bin/env python3
"""Tables and the verdict on each pre-registered prediction (study/PREREGISTRATION.md).

    analyze.py RESULTS.csv [RIC3_VERDICTS.csv] > summary.md

Definitions used below:
  in scope    the reference checker did not refuse the pair (kc is accept or reject)
  P1          no checker accepts a pair whose model is unsafe (cf, co, ca, va)
  P2          the reference checker accepts no pair whose model is unsafe
  P3          in scope, Certifaiger current never accepts what the reference checker rejects
  P4          in scope, every pair the reference checker accepts and Certifaiger current
              rejects is explained by D1, D2 or D3:
                D1  Certifaiger's Transition check frees the witness's private latches at
                    the second time point (kcheck --diag: transD1 = false)
                D2  ... also frees the model's latches outside K there (transD1 = true,
                    transCF = false)
                D3  Certifaiger reports "not stratified" while the reference checker found
                    a semantic stratification
  P5          every pair Certifaiger current accepts and 10.2.1 rejects is one where
              10.2.1 reports "not stratified", and the reference checker accepts it
  P6          the ground truth agrees with rIC3 on every std model both decide
"""
import collections
import csv
import os
import statistics
import sys

# Valaig's own messages (Tools/ValaigCert.lean at 6217ed0a). The harness records every
# non-accepting run as reject_or_error; the log says which it was.
VALAIG_SCOPE = ("model not wellformed", "expected single bad in model",
                "bad not valid in model", "expected single bad in certificate",
                "failed to construct product circuit",
                # added after reading the counted results (DEVIATIONS.md): its parser's
                # refusal of liveness files
                "justice and fairness properties not yet supported")


def valaig_class(r, logs):
    """accept / reject (a check failed) / out of scope (refused before the checks) /
    timeout / error. Without the logs only accept, timeout and other are known."""
    if r["va"] in ("accept", "timeout", "absent"):
        return r["va"]
    p = os.path.join(logs, r["id"], "va.log") if logs else ""
    if not p or not os.path.exists(p):
        return "other"
    t = open(p, errors="replace").read()
    if "s CERTIFICATE UNSAFE" in t:
        return "reject"
    if any(m in t for m in VALAIG_SCOPE):
        return "out of scope"
    return "error"


def pct(a, b):
    return "%.1f%%" % (100.0 * a / b) if b else "-"


def main(argv):
    rows = list(csv.DictReader(open(argv[0])))
    ric3 = {}
    if len(argv) > 1:
        for line in open(argv[1]):
            p = line.strip().split(",")
            if len(p) == 3:
                ric3[p[0]] = p[2]
    out = []
    P = out.append
    n = len(rows)
    P("# Conformance study: summary (%d pairs)\n" % n)

    P("## Corpus\n")
    fam = collections.Counter((r["family"], r["kind"]) for r in rows)
    P("| family | kind | pairs | model safe | model unsafe |")
    P("|---|---|---|---|---|")
    for (f, k), c in sorted(fam.items()):
        s = sum(1 for r in rows if r["family"] == f and r["kind"] == k and r["gt"] == "safe")
        u = sum(1 for r in rows if r["family"] == f and r["kind"] == k and r["gt"] == "unsafe")
        P("| %s | %s | %d | %d | %d |" % (f, k, c, s, u))
    gterr = sum(1 for r in rows if r["gt"] not in ("safe", "unsafe"))
    P("\nGround truth undecided: %d\n" % gterr)

    P("## Scope of the reference checker\n")
    sc = collections.Counter(r["kc"].split(":", 1)[0] for r in rows)
    P("| verdict | pairs |")
    P("|---|---|")
    for k, c in sc.most_common():
        P("| %s | %d |" % (k, c))
    ref = collections.Counter(r["kc"].split(":", 1)[1].split(" (")[0].split(":")[0]
                              for r in rows if r["kc"].startswith("refused:"))
    P("\nRefusal reasons:\n")
    for k, c in ref.most_common():
        P("- %s: %d" % (k, c))
    P("")

    P("## Verdicts (ground truth x reference checker x Certifaiger current x 10.2.1)\n")
    P("| model | reference | current | 10.2.1 | pairs |")
    P("|---|---|---|---|---|")
    for k, c in sorted(collections.Counter(
            (r["gt"], r["kc"].split(":")[0], r["cf"], r["co"]) for r in rows).items(),
            key=lambda x: -x[1]):
        P("| %s | %s | %s | %s | %d |" % (k + (c,)))
    P("")

    P("## Predictions\n")
    res = {}
    viol1 = {k: [r["id"] for r in rows if r[k] == "accept" and r["gt"] == "unsafe"] for k in ("cf", "co", "ca", "va")}
    res["P1"] = all(not v for v in viol1.values())
    P("**P1** no checker accepts an unsafe model: %s  (%s)" % (
        "HOLDS" if res["P1"] else "FALSIFIED",
        ", ".join("%s %d" % (k, len(v)) for k, v in viol1.items())))
    for k, v in viol1.items():
        if v:
            P("  - %s accepts unsafe: %s" % (k, " ".join(v[:20])))
    v2 = [r["id"] for r in rows if r["kc"] == "accept" and r["gt"] == "unsafe"]
    res["P2"] = not v2
    P("**P2** the reference checker accepts no unsafe model: %s (%d)%s" % (
        "HOLDS" if res["P2"] else "FALSIFIED", len(v2), (": " + " ".join(v2[:20])) if v2 else ""))
    insc = [r for r in rows if r["kc"] in ("accept", "reject")]
    v3 = [r["id"] for r in insc if r["cf"] == "accept" and r["kc"] == "reject"]
    res["P3"] = not v3
    P("**P3** in scope (%d pairs), Certifaiger never accepts what the reference rejects: %s (%d)%s" % (
        len(insc), "HOLDS" if res["P3"] else "FALSIFIED", len(v3), (": " + " ".join(v3[:20])) if v3 else ""))
    d = [r for r in insc if r["kc"] == "accept" and r["cf"] == "reject"]
    cls = collections.Counter()
    unexplained = []
    for r in d:
        if r["kc_transD1"] == "0":
            cls["D1"] += 1
        elif r["kc_transD1"] == "1" and r["kc_transCF"] == "0":
            cls["D2"] += 1
        elif r["cf_strat"] == "1" and r["kc_strat"] == "1":
            cls["D3"] += 1
        else:
            unexplained.append(r["id"])
    res["P4"] = not unexplained
    P("**P4** reference accepts, Certifaiger rejects: %d pairs; D1 %d, D2 %d, D3 %d, unexplained %d: %s" % (
        len(d), cls["D1"], cls["D2"], cls["D3"], len(unexplained), "HOLDS" if res["P4"] else "FALSIFIED"))
    if unexplained:
        P("  - unexplained: %s" % " ".join(unexplained[:30]))
    co_rej = [r for r in rows if r["cf"] == "accept" and r["co"] == "reject"]
    v5 = [r["id"] for r in co_rej if not (r["co_strat"] == "1" and r["kc"] == "accept")]
    res["P5"] = not v5
    P("**P5** current accepts, 10.2.1 rejects: %d pairs; all 'not stratified' and accepted by the reference: %s%s" % (
        len(co_rej), "HOLDS" if res["P5"] else "FALSIFIED (%d)" % len(v5), (": " + " ".join(v5[:20])) if v5 else ""))
    by_fam = collections.Counter(r["family"] for r in co_rej)
    P("  - by family: %s" % ", ".join("%s %d" % kv for kv in by_fam.most_common()))
    if ric3:
        gt_by_model = {}
        for r in rows:
            mid = r["model"].split("/")[-1][:-4]
            gt_by_model[mid] = r["gt"]
        both = [(m, v, gt_by_model[m]) for m, v in ric3.items() if v in ("safe", "unsafe") and m in gt_by_model]
        dis = [m for m, v, g in both if v != g]
        res["P6"] = not dis
        P("**P6** ground truth agrees with rIC3 on %d std models both decide: %s (%d disagreements)%s" % (
            len(both), "HOLDS" if res["P6"] else "FALSIFIED", len(dis), (": " + " ".join(dis)) if dis else ""))
    P("")

    P("## Valaig\n")
    logs = os.path.join(os.path.dirname(os.path.abspath(argv[0])), "logs")
    logs = logs if os.path.isdir(logs) else None
    va = collections.Counter(valaig_class(r, logs) for r in rows)
    P("Outcomes (from its messages%s): %s" % ("" if logs else "; logs absent",
                                            ", ".join("%s %d" % kv for kv in va.most_common())))
    vk = collections.Counter((r["kind"], valaig_class(r, logs)) for r in rows)
    P("By model kind: %s" % ", ".join("%s/%s %d" % (k, c, n) for (k, c), n in sorted(vk.items())))
    vacc = [r for r in rows if r["va"] == "accept"]
    P("Valaig accepts %d pairs: Certifaiger current %s, reference %s" % (
        len(vacc), dict(collections.Counter(r["cf"] for r in vacc)),
        dict(collections.Counter(r["kc"].split(":")[0] for r in vacc))))
    both_ok = [r for r in rows if r["cf"] == "accept" and r["va"] != "accept" and r["kind"] == "std"]
    P("Certifaiger accepts and Valaig does not, std models: %d" % len(both_ok))
    P("")

    P("## Robustness\n")
    for k, name in (("cf", "current, release"), ("ca", "current, assertions on"), ("co", "10.2.1")):
        cr = collections.Counter((r["family"], r[k]) for r in rows if r[k] in ("crash", "error", "timeout", "limit"))
        P("- Certifaiger %s: %s" % (name, ", ".join("%s/%s %d" % (f, v, c) for (f, v), c in cr.most_common()) or "none"))
    rcs = collections.Counter((r["family"], r["cf_rc"]) for r in rows if r["cf"] in ("error", "crash"))
    P("- current, release, exit codes on errors: %s" % ", ".join("%s rc=%s %d" % (f, c, k) for (f, c), k in rcs.most_common()))
    P("")

    P("## Cost\n")
    t = sorted(float(r["kc_t"]) for r in rows if r["kc"] in ("accept", "reject"))
    tc = sorted(float(r["cf_t"]) for r in rows if r["cf"] in ("accept", "reject"))
    if t:
        P("Reference checker (front end + kcheck), in scope: median %.3f s, 90th %.3f s, max %.3f s" % (
            statistics.median(t), t[int(0.9 * (len(t) - 1))], t[-1]))
    if tc:
        P("Certifaiger current: median %.3f s, 90th %.3f s, max %.3f s" % (
            statistics.median(tc), tc[int(0.9 * (len(tc) - 1))], tc[-1]))
    P("")
    P("Predictions: " + ", ".join("%s %s" % (k, "holds" if v else "FALSIFIED") for k, v in sorted(res.items())))
    print("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
