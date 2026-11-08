#!/usr/bin/env python3
"""Every number the manuscript reports about the study, from the results files.

    make_tables.py RESULTS.csv RESULTS_FIXED.csv RIC3_VERDICTS.csv OUTDIR [CORPUS FIXED_CORPUS]

Writes OUTDIR/numbers.tex (one \\newcommand per number) and OUTDIR/tab_*.tex (tables).
With the two corpus directories it also compares Valaig's refusals with its documented
scope, read from the files.
The manuscript uses only these macros for study numbers, so a rerun updates every place.
"""
import collections
import csv
import os
import statistics
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from analyze import valaig_class  # noqa: E402  (one definition for both scripts)


def aag_info(path):
    """What Valaig's documented scope depends on, read from an ASCII AIGER file:
    bad and constraint counts, and its well-formedness (Valaig/Aig/Core/Lemmas/
    WellFormed.lean at 6217ed0a): every gate reads lower-numbered variables, and every
    reset literal other than the latch itself has a lower variable than its latch."""
    with open(path, "rb") as f:
        data = f.read()
    lines = data.split(b"\n")
    h = lines[0].split()
    binary = h[0] == b"aig"
    M, I, L, O, A = (int(x) for x in h[1:6])
    B = int(h[6]) if len(h) > 6 else 0
    C = int(h[7]) if len(h) > 7 else 0
    J = int(h[8]) if len(h) > 8 else 0
    F = int(h[9]) if len(h) > 9 else 0
    wf = True
    # binary files list no inputs and give each latch as "next [reset]"; their gates are
    # ordered by the format
    first_latch = 1 if binary else 1 + I
    for k, ln in enumerate(lines[first_latch:first_latch + L]):
        p = [int(x) for x in ln.split()]
        lit = 2 * (I + 1 + k) if binary else p[0]
        rst = p[1] if binary and len(p) > 1 else (p[2] if not binary and len(p) > 2 else 0)
        if rst not in (0, 1, lit) and rst // 2 >= lit // 2:
            wf = False
    if not binary:
        pos = first_latch + L + O + B + C
        sizes = [int(x) for x in lines[pos:pos + J]]
        first_gate = pos + J + sum(sizes) + F
        for ln in lines[first_gate:first_gate + A]:
            p = [int(x) for x in ln.split()]
            if p[1] // 2 >= p[0] // 2 or p[2] // 2 >= p[0] // 2:
                wf = False
    return {"B": B, "C": C, "live": J + F > 0, "wf": wf}


def parse_aag(path):
    """Latches, bad and constraint literals, gates and '= n' latch symbols of an ASCII
    AIGER file without liveness sections (the generated corpus)."""
    lines = open(path).read().split("\n")
    h = lines[0].split()
    I, L, O, A = (int(x) for x in h[2:6])
    B = int(h[6]) if len(h) > 6 else 0
    C = int(h[7]) if len(h) > 7 else 0
    lat = [[int(x) for x in ln.split()] for ln in lines[1 + I:1 + I + L]]
    rest = lines[1 + I + L:]
    bads, cons = rest[O:O + B], rest[O + B:O + B + C]
    gates = {int(ln.split()[0]) // 2: [int(x) for x in ln.split()[1:]] for ln in rest[O + B + C:O + B + C + A]}
    mapped = set()
    for s in rest[O + B + C + A:]:
        if s.startswith("l"):
            k, _, v = s.partition(" ")
            if v.startswith("= "):
                mapped.add(int(k[1:]))
    return {"lat": lat, "bads": bads, "cons": cons, "gates": gates, "mapped": mapped}


def valaig_view(path):
    """What Valaig reads of a witness (External/Cert/Product.lean at 6217ed0a): a latch
    with an '= n' symbol is replaced by the model's literal and its reset and next are
    never read; the unmapped latches, the bad and constraint literals and the gates in
    their fan-in are."""
    w = parse_aag(path)
    priv = [k for k in range(len(w["lat"])) if k not in w["mapped"]]
    roots = [int(b.split()[0]) for b in w["bads"]] + [int(c.split()[0]) for c in w["cons"]]
    for k in priv:
        roots += w["lat"][k][1:]
    seen, stack = set(), [r // 2 for r in roots]
    while stack:
        v = stack.pop()
        if v not in seen:
            seen.add(v)
            stack += [x // 2 for x in w["gates"].get(v, [])]
    return (tuple(sorted(w["mapped"])), tuple(tuple(w["lat"][k]) for k in priv),
            tuple(w["bads"]), tuple(w["cons"]),
            tuple(sorted((v, tuple(w["gates"][v])) for v in seen if v in w["gates"])))


def reset_cycle(path):
    """(has a cycle, has a reset that reads its own latch) in the syntactic reset
    dependency graph of an ASCII AIGER file, through gates; an uninitialized latch (reset
    literal = the latch) is not an edge, as in Certifaiger's test."""
    w = parse_aag(path)
    lv = {l[0] // 2: k for k, l in enumerate(w["lat"])}
    def deps(lit):
        out, seen, stack = set(), set(), [lit // 2]
        while stack:
            v = stack.pop()
            if v in seen:
                continue
            seen.add(v)
            if v in lv:
                out.add(lv[v])
            else:
                stack += [x // 2 for x in w["gates"].get(v, [])]
        return out
    E = {k: (deps(l[2]) if len(l) > 2 and l[2] not in (0, 1, l[0]) else set()) for k, l in enumerate(w["lat"])}
    color = {}
    def dfs(u):
        color[u] = 1
        for v in E[u]:
            if color.get(v) == 1 or (color.get(v) is None and dfs(v)):
                return True
        color[u] = 2
        return False
    return any(color.get(k) is None and dfs(k) for k in E), any(k in E[k] for k in E)


def valaig_expected_out_of_scope(model, witness):
    m, w = aag_info(model), aag_info(witness)
    return (not m["wf"] or m["B"] != 1 or not w["wf"] or w["B"] != 1 or w["C"] > 0
            or m["live"] or w["live"])


DIGITS = "Zero One Two Three Four Five Six Seven Eight Nine".split()


def macro_name(key):
    """A LaTeX command name: letters only, so digits are spelled (d1_pairs -> NDOnePairs)."""
    words = key.replace("-", "_").split("_")
    name = "N" + "".join(w[:1].upper() + w[1:] for w in words)
    return "".join(DIGITS[int(c)] if c.isdigit() else c for c in name)


def fmt(x):
    if isinstance(x, float):
        return "%.3f" % x
    return "{:,}".format(x).replace(",", "{,}")


def main(argv):
    rows = list(csv.DictReader(open(argv[0])))
    fixed = list(csv.DictReader(open(argv[1]))) if os.path.exists(argv[1]) else []
    ric3 = {}
    for line in open(argv[2]):
        p = line.strip().split(",")
        if len(p) == 3:
            ric3[p[0]] = p[2]
    out = argv[3]
    os.makedirs(out, exist_ok=True)
    N = {}
    allr = rows + fixed
    # the logs of the generated pairs sit beside results.csv, those of the fixed pairs too
    logs = os.path.join(os.path.dirname(os.path.abspath(argv[0])), "logs")
    logs = logs if os.path.isdir(logs) else None
    va = {r["id"]: valaig_class(r, logs) for r in allr}
    kc = lambda r: r["kc"].split(":", 1)[0]
    N["pairs"] = len(allr)
    N["generated"] = len(rows)
    N["fixed"] = len(fixed)
    models = {r["model"] for r in rows if r["family"] not in ("mmut",)}
    N["models"] = len({m for m in models if "/m" in m and "_" not in m.split("/")[-1]})
    N["ric3_safe"] = sum(1 for v in ric3.values() if v == "safe")
    N["ric3_unsafe"] = sum(1 for v in ric3.values() if v == "unsafe")
    N["ric3_other"] = sum(1 for v in ric3.values() if v not in ("safe", "unsafe"))
    N["unsafe_pairs"] = sum(1 for r in allr if r["gt"] == "unsafe")
    N["safe_pairs"] = sum(1 for r in allr if r["gt"] == "safe")
    N["gt_undecided"] = sum(1 for r in allr if r["gt"] not in ("safe", "unsafe"))
    insc = [r for r in allr if kc(r) in ("accept", "reject")]
    N["in_scope"] = len(insc)
    N["refused"] = sum(1 for r in allr if kc(r) == "refused")
    N["kc_error"] = sum(1 for r in allr if kc(r) == "error")
    reasons = collections.Counter()
    for r in allr:
        if kc(r) == "refused":
            reason = r["kc"].split(":", 1)[1]
            if "enumeration budget" in reason:
                reason = "enumeration budget"
            elif "reads a later or undefined" in reason:
                reason = "gate order"
            elif "not reencoded" in reason:
                reason = "not reencoded"
            elif "malformed" in reason:
                reason = "malformed"
            reasons[reason] += 1
    # P1, P2
    for k in ("cf", "ca", "co", "va", "kc"):
        N["%s_accept_unsafe" % k] = sum(1 for r in allr if (kc(r) if k == "kc" else r[k]) == "accept" and r["gt"] == "unsafe")
        N["%s_accept" % k] = sum(1 for r in allr if (kc(r) if k == "kc" else r[k]) == "accept")
    # conformance in scope
    N["agree_accept"] = sum(1 for r in insc if kc(r) == "accept" and r["cf"] == "accept")
    N["agree_reject"] = sum(1 for r in insc if kc(r) == "reject" and r["cf"] == "reject")
    N["kc_acc_cf_rej"] = sum(1 for r in insc if kc(r) == "accept" and r["cf"] == "reject")
    N["cf_acc_kc_rej"] = sum(1 for r in insc if kc(r) == "reject" and r["cf"] == "accept")
    N["in_scope_cf_other"] = sum(1 for r in insc if r["cf"] not in ("accept", "reject"))
    d = [r for r in insc if kc(r) == "accept" and r["cf"] == "reject"]
    N["d1"] = sum(1 for r in d if r["kc_transD1"] == "0")
    N["d2"] = sum(1 for r in d if r["kc_transD1"] == "1" and r["kc_transCF"] == "0")
    N["d3"] = sum(1 for r in d if not (r["kc_transD1"] == "0" or (r["kc_transD1"] == "1" and r["kc_transCF"] == "0"))
                  and r["cf_strat"] == "1" and r["kc_strat"] == "1")
    N["d_unexplained"] = len(d) - N["d1"] - N["d2"] - N["d3"]
    is_d3 = lambda r: (r in d and r["kc_transD1"] != "0" and not (r["kc_transD1"] == "1" and r["kc_transCF"] == "0")
                       and r["cf_strat"] == "1" and r["kc_strat"] == "1")
    # Certifaiger's syntactic stratification test against the semantic condition: wherever
    # the test passed on a pair both decided, did the reference checker find a stratification?
    for k in ("cf", "co"):
        passed = [r for r in insc if r[k] in ("accept", "reject") and r[k + "_strat"] == "0"]
        N["strat_%s_pass" % k] = len(passed)
        N["strat_%s_pass_kc_strat" % k] = sum(1 for r in passed if r["kc_strat"] == "1")
    # the unsafe pairs: how many Certifaiger turned away before any check
    N["unsafe_cf_notstrat"] = sum(1 for r in allr if r["gt"] == "unsafe" and r["cf"] == "reject"
                                  and r["cf_strat"] == "1" and r["cf_failed"] == "")
    # our encoding of Certifaiger's Transition check against what Certifaiger reports
    N["d1_cf_names_trans"] = sum(1 for r in d if r["kc_transD1"] == "0" and r["kc_transCF"] == "0"
                                 and "Transition" in r["cf_failed"])
    N["d3_transcf_passes"] = sum(1 for r in d if r["kc_transD1"] != "0" and r["kc_transCF"] == "1"
                                 and r["cf_failed"] == "" and r["cf_strat"] == "1")
    # the September change
    ch = [r for r in allr if r["cf"] == "accept" and r["co"] == "reject"]
    N["change"] = len(ch)
    N["change_strat"] = sum(1 for r in ch if r["co_strat"] == "1")
    N["change_kc_accept"] = sum(1 for r in ch if kc(r) == "accept")
    N["change_kc_refused"] = sum(1 for r in ch if kc(r) == "refused")
    N["co_acc_cf_rej"] = sum(1 for r in allr if r["co"] == "accept" and r["cf"] == "reject")
    for f, c in collections.Counter(r["family"] for r in ch).items():
        N["change_" + f] = c
    # expectations by family
    fam = lambda f: [r for r in allr if r["family"] == f]
    N["d1_pairs"] = len(fam("d1"))
    N["d1_cf_trans"] = sum(1 for r in fam("d1") if "Transition" in r["cf_failed"])
    N["d1_kc_accept"] = sum(1 for r in fam("d1") if kc(r) == "accept")
    N["d3_pairs"] = len(fam("d3"))
    N["d3_cf_strat"] = sum(1 for r in fam("d3") if r["cf_strat"] == "1")
    N["d3_co_strat"] = sum(1 for r in fam("d3") if r["co_strat"] == "1")
    N["d3_kc_accept"] = sum(1 for r in fam("d3") if kc(r) == "accept")
    N["kp_pairs"] = len(fam("kp"))
    N["kp_cf_accept"] = sum(1 for r in fam("kp") if r["cf"] == "accept")
    N["kp_co_strat"] = sum(1 for r in fam("kp") if r["co_strat"] == "1")
    N["kp_kc_accept"] = sum(1 for r in fam("kp") if kc(r) == "accept")
    N["kp_rej_both_strat"] = sum(1 for r in fam("kp") if r["cf"] == "reject" and r["cf_strat"] == "1"
                                 and kc(r) == "reject" and r["kc_strat"] == "0")
    o = fam("order")
    N["order_pairs"] = len(o)
    for k in ("cf", "ca", "co"):
        for v in ("accept", "reject", "limit", "crash", "error", "timeout"):
            N["order_%s_%s" % (k, v)] = sum(1 for r in o if r[k] == v)
    killed = [float(r["cf_t"]) for r in o if r["cf"] == "error" and r["cf_rc"] == "1" and r["cf_t"]]
    if killed:
        N["order_cf_kill_t_max"] = max(killed)
    N["order_kc_refused"] = sum(1 for r in o if kc(r) == "refused")
    # non-verdicts of the three Certifaiger builds, whole corpus
    for k in ("cf", "ca", "co"):
        for v in ("limit", "crash", "error", "timeout"):
            N["%s_%s" % (k, v)] = sum(1 for r in allr if r[k] == v)
    # Valaig, by its own messages
    for c in ("reject", "out of scope", "error", "timeout", "other"):
        N["va_" + c.replace(" ", "_")] = sum(1 for r in allr if va[r["id"]] == c)
    N["va_decided"] = sum(1 for r in allr if va[r["id"]] in ("accept", "reject"))
    N["va_decided_std"] = sum(1 for r in allr if va[r["id"]] in ("accept", "reject") and r["kind"] == "std")
    N["va_decided_ext"] = sum(1 for r in allr if va[r["id"]] in ("accept", "reject") and r["kind"] == "ext")
    # Valaig's refusals against its documented scope, when the corpora are at hand
    corpora = [(rows, argv[4] if len(argv) > 4 else None), (fixed, argv[5] if len(argv) > 5 else None)]
    if all(cdir_ for rr, cdir_ in corpora if rr):
        exp = {}
        for rr, cdir_ in corpora:
            for r in rr:
                exp[r["id"]] = valaig_expected_out_of_scope(os.path.join(cdir_, r["model"]),
                                                            os.path.join(cdir_, r["witness"]))
        N["va_scope_expected"] = sum(1 for r in allr if exp[r["id"]])
        N["va_scope_match"] = sum(1 for r in allr if exp[r["id"]] == (va[r["id"]] == "out of scope"))
        N["va_scope_mismatch"] = len(allr) - N["va_scope_match"]
        # Valaig accepts, Certifaiger does not: which are model mutants, and which witness
        # mutants change nothing Valaig reads (diff against the base witness)
        cdir = argv[4]
        man = {r["id"]: r for r in csv.DictReader(open(os.path.join(cdir, "manifest.csv")))}
        vo = [r for r in allr if r["va"] == "accept" and r["cf"] != "accept"]
        N["va_only"] = len(vo)
        N["va_only_mmut"] = sum(1 for r in vo if r["family"] == "mmut")
        wm = [r for r in vo if r["family"] == "mut"]
        N["va_only_mut"] = len(wm)
        N["va_only_mut_unread"] = sum(
            1 for r in wm if valaig_view(os.path.join(cdir, r["witness"]))
            == valaig_view(os.path.join(cdir, man[man[r["id"]]["base"]]["witness"])))
        N["va_only_other"] = len(vo) - N["va_only_mmut"] - N["va_only_mut"]
        N["va_only_kc_reject"] = sum(1 for r in vo if kc(r) == "reject")
        N["va_only_kc_refused"] = sum(1 for r in vo if kc(r) == "refused")
        # root family of every pair (mutants trace back through `base`)
        def root(i):
            while man[i]["base"]:
                i = man[i]["base"]
            return man[i]["family"]
        gen_d = [r for r in d if r["id"] in man]
        N["d1_root_d1"] = sum(1 for r in gen_d if r["kc_transD1"] == "0" and root(r["id"]) == "d1")
        N["d3_root_d3"] = sum(1 for r in gen_d if is_d3(r) and root(r["id"]) == "d3")
        N["d3_root_other"] = sum(1 for r in gen_d if is_d3(r) and root(r["id"]) != "d3")
        # exact witnesses newly admitted: their copied resets have a dependency cycle
        ex_ch = [r for r in ch if r["id"] in man and root(r["id"]) == "exact"]
        cyc = [reset_cycle(os.path.join(cdir, r["witness"])) for r in ex_ch]
        N["change_root_exact_cycle"] = sum(1 for c, s in cyc if c)
        N["change_root_exact_selfread"] = sum(1 for c, s in cyc if s)
        # Valaig decides pairs whose model has constraints (it refuses them only in witnesses)
        dir_of = {r["id"]: (cdir if r["id"] in man else argv[5]) for r in allr}
        N["va_decided_model_cons"] = sum(
            1 for r in allr if va[r["id"]] in ("accept", "reject")
            and aag_info(os.path.join(dir_of[r["id"]], r["model"]))["C"] > 0)
        # the size of the drawn models
        import re as _re
        mdir = os.path.join(cdir, "models")
        sizes = [aag_info(os.path.join(mdir, f)) for f in os.listdir(mdir) if _re.fullmatch(r"m\d{4}\.aag", f)]
        N["models_drawn"] = len(sizes)
        hdr = [open(os.path.join(mdir, f)).readline().split() for f in os.listdir(mdir) if _re.fullmatch(r"m\d{4}\.aag", f)]
        N["max_inputs"] = max(int(h[2]) for h in hdr)
        N["max_latches"] = max(int(h[3]) for h in hdr)
        N["max_gates"] = max(int(h[5]) for h in hdr)
        for f, c in collections.Counter(root(r["id"]) for r in ch if r["id"] in man).items():
            N["change_root_" + f] = c
        N["kp_same_verdict"] = sum(1 for r in fam("kp") if (r["cf"] == "accept") == (kc(r) == "accept"))
        # renumbered witnesses against the same witness with ordered gates (its base)
        byid = {r["id"]: r for r in rows}
        o_ = [r for r in rows if r["family"] == "order"]
        N["order_base_cf_accept"] = sum(1 for r in o_ if byid[man[r["id"]]["base"]]["cf"] == "accept")
        N["order_verdict_differs"] = sum(
            1 for r in o_ for k in ("cf", "ca", "co")
            if r[k] in ("accept", "reject") and r[k] != byid[man[r["id"]]["base"]][k])
        def has_mapping_symbol(path):
            return any(ln[:1] in ("i", "l") and " = " in ln for ln in open(path).read().split("\n"))
        N["va_reject_cf_accept_nosym"] = sum(
            1 for r in allr if va[r["id"]] == "reject" and r["cf"] == "accept"
            and not has_mapping_symbol(os.path.join(dir_of[r["id"]], r["witness"])))
    N["va_reject_cf_accept"] = sum(1 for r in allr if va[r["id"]] == "reject" and r["cf"] == "accept")
    N["va_reject_kc_accept"] = sum(1 for r in allr if va[r["id"]] == "reject" and kc(r) == "accept")
    # the differences D1 and D3, by family
    for f in ("d1", "d3", "mut", "mmut", "aux", "exact", "kp", "ric3"):
        N["d1_" + f] = sum(1 for r in d if r["family"] == f and r["kc_transD1"] == "0")
        N["d3_" + f] = sum(1 for r in d if r["family"] == f and r["kc_transD1"] != "0"
                               and r["cf_strat"] == "1" and r["kc_strat"] == "1")
    N["va_accept_total"] = N["va_accept"]
    vacc = [r for r in allr if r["va"] == "accept"]
    N["va_accept_cf_accept"] = sum(1 for r in vacc if r["cf"] == "accept")
    N["va_accept_kc_accept"] = sum(1 for r in vacc if kc(r) == "accept")
    std_nc = [r for r in allr if r["kind"] == "std" and r["cf"] == "accept"]
    N["cf_accept_std"] = len(std_nc)
    N["cf_accept_std_va_accept"] = sum(1 for r in std_nc if r["va"] == "accept")
    # Certifaiger's own test pairs
    cft = [r for r in allr if r["family"] == "certifaiger-tests"]
    N["cft_pairs"] = len(cft)
    N["cft_in_scope"] = sum(1 for r in cft if kc(r) in ("accept", "reject"))
    # post hoc: renumbered witnesses converted to binary AIGER and checked again
    obin = os.path.join(os.path.dirname(os.path.abspath(argv[0])), "posthoc_order_binary.csv")
    if os.path.exists(obin):
        ob = list(csv.DictReader(open(obin)))
        N["order_bin_n"] = len(ob)
        N["order_bin_same"] = sum(1 for r in ob if r["binary_verdict"] == r["ordered_verdict"])
        N["order_bin_accept"] = sum(1 for r in ob if r["binary_verdict"] == "accept")
    # post hoc: Certifaiger 10.4.1, released after the run, on every pair (posthoc_cf1041.py)
    later = os.path.join(os.path.dirname(os.path.abspath(argv[0])), "posthoc_cf1041.csv")
    if os.path.exists(later):
        lr = list(csv.DictReader(open(later)))
        N["later_n"] = len(lr)
        N["later_same"] = sum(1 for r in lr if r["same_verdict"] == "1")
        N["later_same_reason"] = sum(1 for r in lr if r["same_reason"] == "1")
        N["later_accept"] = sum(1 for r in lr if r["new"] == "accept")
        N["later_order_no_verdict"] = sum(1 for r in lr if r["family"] == "order"
                                          and r["new"] not in ("accept", "reject"))
        N["later_order_accept"] = sum(1 for r in lr if r["family"] == "order" and r["new"] == "accept")
    # P6, and the exploratory check on every model rIC3 ran on
    p6x = os.path.join(os.path.dirname(os.path.abspath(argv[0])), "p6_all_models.csv")
    if os.path.exists(p6x):
        x = [ln.strip().split(",") for ln in open(p6x) if ln.strip()]
        N["p6x_models"] = len(x)
        N["p6x_agree"] = sum(1 for m, v, g in x if v == g)
    gt_by_model = {}
    for r in rows:
        mid = r["model"].split("/")[-1][:-4]
        gt_by_model[mid] = r["gt"]
    both = [(m, v) for m, v in ric3.items() if v in ("safe", "unsafe") and m in gt_by_model]
    N["p6_models"] = len(both)
    N["p6_disagree"] = sum(1 for m, v in both if gt_by_model[m] != v)
    # cost
    tk = sorted(float(r["kc_t"]) for r in insc if r["kc_t"])
    tc = sorted(float(r["cf_t"]) for r in allr if r["cf"] in ("accept", "reject") and r["cf_t"])
    if tk:
        N["kc_t_n"] = len(tk)
        N["kc_t_median"] = statistics.median(tk)
        N["kc_t_p90"] = tk[int(0.9 * (len(tk) - 1))]
        N["kc_t_max"] = tk[-1]
    if tc:
        N["cf_t_n"] = len(tc)
        N["cf_t_median"] = statistics.median(tc)
        N["cf_t_p90"] = tc[int(0.9 * (len(tc) - 1))]
        N["cf_t_max"] = tc[-1]
    with open(os.path.join(out, "numbers.tex"), "w") as f:
        f.write("%% generated by study/make_tables.py; do not edit\n")
        for k in sorted(N):
            f.write("\\newcommand{\\%s}{%s}\n" % (macro_name(k), fmt(N[k])))
        for k, c in sorted(reasons.items()):
            f.write("\\newcommand{\\%s}{%s}\n" % (macro_name("refused_" + "".join(ch if ch.isalnum() else "_" for ch in k)), fmt(c)))
    # Table: verdicts by family
    order = ["exact", "aux", "kp", "d1", "d3", "ric3", "mut", "mmut", "order", "certifaiger-tests", "handmade"]
    with open(os.path.join(out, "tab_families.tex"), "w") as f:
        f.write("%% generated by study/make_tables.py; do not edit\n")
        f.write("\\begin{tabular}{@{}lrrrrrrrr@{}}\n\\toprule\n")
        f.write("Family & Pairs & Unsafe & \\multicolumn{2}{c}{Reference} & \\multicolumn{2}{c}{Certifaiger} & 10.2.1 & Valaig\\\\\n")
        f.write(" & & model & acc. & refused & acc. & rej. & acc. & acc.\\\\\n\\midrule\n")
        for fm in order:
            rr = [r for r in allr if r["family"] == fm]
            if not rr:
                continue
            f.write("%s & %s & %s & %s & %s & %s & %s & %s & %s\\\\\n" % (
                fm.replace("-", " "), fmt(len(rr)), fmt(sum(1 for r in rr if r["gt"] == "unsafe")),
                fmt(sum(1 for r in rr if kc(r) == "accept")), fmt(sum(1 for r in rr if kc(r) == "refused")),
                fmt(sum(1 for r in rr if r["cf"] == "accept")), fmt(sum(1 for r in rr if r["cf"] == "reject")),
                fmt(sum(1 for r in rr if r["co"] == "accept")),
                fmt(sum(1 for r in rr if r["va"] == "accept"))))
        f.write("\\midrule\nAll & %s & %s & %s & %s & %s & %s & %s & %s\\\\\n\\bottomrule\n\\end{tabular}\n" % (
            fmt(len(allr)), fmt(N["unsafe_pairs"]), fmt(N["kc_accept"]), fmt(N["refused"]),
            fmt(N["cf_accept"]), fmt(sum(1 for r in allr if r["cf"] == "reject")), fmt(N["co_accept"]),
            fmt(N["va_accept"])))
    # Table: verdict combinations (ground truth, reference, Certifaiger 10.4.0, 10.2.1)
    word = {"accept": "acc.", "reject": "rej.", "refused": "refused", "error": "no verdict",
            "limit": "no verdict", "crash": "no verdict", "timeout": "no verdict"}
    combos = collections.Counter((r["gt"], kc(r), word.get(r["cf"], r["cf"]), word.get(r["co"], r["co"]))
                                 for r in allr)
    with open(os.path.join(out, "tab_verdicts.tex"), "w") as f:
        f.write("%% generated by study/make_tables.py; do not edit\n")
        f.write("\\begin{tabular}{@{}llllr@{}}\n\\toprule\n")
        f.write("Model & Reference & 10.4.0 & 10.2.1 & Pairs\\\\\n\\midrule\n")
        for (g, k, c1, c2), n in sorted(combos.items(), key=lambda x: -x[1]):
            f.write("%s & %s & %s & %s & %s\\\\\n" % (g if g in ("safe", "unsafe") else "undecided",
                                                     word.get(k, k), c1, c2, fmt(n)))
        f.write("\\midrule\nAll & & & & %s\\\\\n\\bottomrule\n\\end{tabular}\n" % fmt(len(allr)))
    # Table: refusal reasons
    with open(os.path.join(out, "tab_refusals.tex"), "w") as f:
        f.write("%% generated by study/make_tables.py; do not edit\n")
        f.write("\\begin{tabular}{@{}lr@{}}\n\\toprule\nReason & Pairs\\\\\n\\midrule\n")
        for k, c in reasons.most_common():
            f.write("%s & %s\\\\\n" % (k, fmt(c)))
        f.write("\\bottomrule\n\\end{tabular}\n")
    print("wrote %d numbers and 3 tables to %s" % (len(N) + len(reasons), out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
