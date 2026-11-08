#!/usr/bin/env python3
"""Corpus of model-witness pairs for the conformance study. Deterministic from a seed.

    make_corpus.py stage1 OUT --seed S --models N     models, built witnesses, mutants
    make_corpus.py stage3 OUT --seed S                 mutants of rIC3's certificates
                                                       (OUT/ric3/*.cert.aag, made in between
                                                       by study/gen/ric3_certificates.sh)

Families (column `family` of OUT/manifest.csv):
  exact   witness = model plus the reachable-state invariant (every latch and input shared)
  aux     exact witness plus one or two private latches with random reset and next functions
  kp      aux witness in which a shared latch's reset reads a private latch whose own reset
          reads that shared latch (a cycle only through a shared latch: accepted by the
          side condition of Certifaiger 10.3.0, rejected by 10.2.1)
  ric3    certificate written by rIC3 for a model it proved safe
  d1      exact witness plus a private latch p that stays low and the witness constraint
          (NOT k OR NOT p) for a shared latch k that resets low: sound, but Certifaiger's
          Transition check lets p be high at the second time point (divergence D1)
  d3      exact witness plus private latches p1, p2 with p1 resetting to (p2 AND NOT p2)
          and p2 to p1: a reset cycle in the syntax only (divergence D3)
  mut     one mutation of an exact, aux, kp, d1, d3 or ric3 witness (column `operator`)
  mmut    one mutation of the model, witness unchanged (a soundness probe)
  order   a valid witness renumbered so that some gate reads a later variable (format probe)
Models come in two kinds (column `kind`): std (resets 0, 1, uninitialized: plain AIGER 1.9)
and ext (also resets to latches, gates, inputs, negated latches: Certifaiger's extension).
"""
import argparse
import csv
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from aig import Circuit, from_aag, reach_overapprox  # noqa: E402

RESET_STD = [("zero", 50), ("one", 25), ("uninit", 25)]
RESET_EXT = [("zero", 30), ("one", 15), ("uninit", 15), ("latch", 12), ("gate", 12),
             ("input", 10), ("neglatch", 6)]
OPERATORS = ["and_input", "reset", "next", "constraint", "bad", "mapping", "uninit"]


def pick(rng, weighted):
    total = sum(w for _, w in weighted)
    x = rng.uniform(0, total)
    for name, w in weighted:
        x -= w
        if x <= 0:
            return name
    return weighted[-1][0]


def reset_literal(rng, c, j, kind, gates):
    nI, nL = c.n_inputs, len(c.latches)
    if kind == "one":
        return 1
    if kind == "uninit":
        return c.latch_lit(j)
    if kind == "neglatch":
        return c.latch_lit(j) ^ 1
    if kind == "latch" and nL > 1:
        return c.latch_lit(rng.choice([k for k in range(nL) if k != j])) ^ rng.randint(0, 1)
    if kind == "gate" and gates:
        return rng.choice(gates) ^ rng.randint(0, 1)
    if kind == "input" and nI > 0:
        return c.input_lit(rng.randrange(nI)) ^ rng.randint(0, 1)
    return 0


def random_model(rng, kind):
    nI, nL, nA = rng.randint(0, 2), rng.randint(1, 4), rng.randint(1, 10)
    c = Circuit(nI)
    for _ in range(nL):
        c.add_latch()
    pool = [c.input_lit(i) for i in range(nI)] + [c.latch_lit(j) for j in range(nL)]
    gates = []
    for _ in range(nA):
        g = c.add_and(rng.choice(pool) ^ rng.randint(0, 1), rng.choice(pool) ^ rng.randint(0, 1))
        pool.append(g)
        gates.append(g)
    for j in range(nL):
        c.latches[j][0] = rng.choice(pool) ^ rng.randint(0, 1)
        c.latches[j][1] = reset_literal(rng, c, j, pick(rng, RESET_STD if kind == "std" else RESET_EXT), gates)
    if rng.random() < 0.6:     # a conjunction is reached less often, so more models are safe
        c.bad = [c.add_and(rng.choice(pool) ^ rng.randint(0, 1), rng.choice(pool) ^ rng.randint(0, 1))]
    else:
        c.bad = [rng.choice(pool) ^ rng.randint(0, 1)]
    if rng.random() < 0.35:
        c.constraints = [rng.choice(pool) ^ rng.randint(0, 1)]
    return c


def with_extra_latches(c, k):
    """The same circuit with k more latches appended (next 0, reset 0); gate literals move up."""
    shift = 2 * k
    old_top = 2 * (c.n_inputs + len(c.latches))

    def mv(x):
        return x + shift if x >= old_top + 2 else x

    d = Circuit(c.n_inputs)
    d.latches = [[mv(n), mv(r)] for n, r in c.latches] + [[0, 0] for _ in range(k)]
    d.ands = [(mv(a), mv(b), mv(e)) for a, b, e in c.ands]
    d.bad = [mv(x) for x in c.bad]
    d.constraints = [mv(x) for x in c.constraints]
    d.symbols = list(c.symbols)
    d.comments = list(c.comments)
    return d


def exact_witness(m, rng):
    """None when the over-approximated reachable set meets a bad configuration."""
    reach, bad = reach_overapprox(m)
    if bad:
        return None
    w = m.copy()
    lat = [w.latch_lit(j) for j in range(len(w.latches))]
    terms = [w.add_and_all([l if s[j] else l ^ 1 for j, l in enumerate(lat)]) for s in sorted(reach)]
    inv = w.add_or_all(terms)
    w.bad = [w.add_or(inv ^ 1, m.bad[0])]
    if rng.random() < 0.5:   # half the witnesses spell the default mapping out as '=' symbols
        w.symbols = ["i%d = %d" % (i, w.input_lit(i)) for i in range(w.n_inputs)]
        w.symbols += ["l%d = %d" % (j, w.latch_lit(j)) for j in range(len(w.latches))]
    w.comments = ["exact witness: model plus its reachable-state invariant"]
    return w


def aux_witness(m, base, rng, kp=False):
    k = rng.randint(1, 2)
    w = with_extra_latches(base, k)
    w.symbols = [s for s in w.symbols if not s.startswith("l")] + \
        ["l%d = %d" % (j, m.latch_lit(j)) for j in range(len(m.latches)) if base.symbols]
    nL0 = len(m.latches)
    shared = [w.latch_lit(j) for j in range(nL0)]
    private = [w.latch_lit(nL0 + i) for i in range(k)]
    ins = [w.input_lit(i) for i in range(w.n_inputs)]
    for i, p in enumerate(private):
        j = nL0 + i
        w.latches[j][0] = rng.choice(shared + private + ins + [0, 1]) ^ rng.randint(0, 1)
        kind = rng.choice(["zero", "one", "uninit", "input", "shared", "private", "gate"])
        if kind == "one":
            r = 1
        elif kind == "uninit":
            r = p
        elif kind == "input" and ins:
            r = rng.choice(ins) ^ rng.randint(0, 1)
        elif kind == "shared":
            r = rng.choice(shared) ^ rng.randint(0, 1)
        elif kind == "private":
            r = rng.choice(private) ^ rng.randint(0, 1)
        elif kind == "gate":
            r = w.add_and(rng.choice(shared + private) ^ rng.randint(0, 1),
                          rng.choice(shared + ins + [1]) ^ rng.randint(0, 1))
        else:
            r = 0
        w.latches[j][1] = r
    if kp:
        j = rng.randrange(nL0)
        p = private[0]
        r = w.latches[j][1]
        # semantically r, syntactically reading p: (r & p) | (r & !p)
        w.latches[j][1] = w.add_or(w.add_and(r, p), w.add_and(r, p ^ 1))
        w.latches[nL0][1] = shared[j]          # p resets to that shared latch
    w.comments = ["%s witness: exact witness plus %d private latch(es)" % ("kp" if kp else "aux", k)]
    return w


def _privatized(m, base, k):
    w = with_extra_latches(base, k)
    if base.symbols:
        w.symbols = [s for s in w.symbols if not s.startswith("l")] + \
            ["l%d = %d" % (j, m.latch_lit(j)) for j in range(len(m.latches))]
    return w


def d1_witness(m, base, rng):
    low = [j for j in range(len(m.latches)) if m.latches[j][1] == 0]
    if not low:
        return None
    j = rng.choice(low)
    w = _privatized(m, base, 1)
    nL0 = len(m.latches)
    w.latches[nL0] = [0, 0]                    # p resets low and stays low
    k, p = w.latch_lit(j), w.latch_lit(nL0)
    w.constraints = w.constraints + [w.add_or(k ^ 1, p ^ 1)]
    w.comments = ["d1 witness: private latch stays low; constraint NOT k OR NOT p"]
    return w


def d3_witness(m, base, rng):
    w = _privatized(m, base, 2)
    nL0 = len(m.latches)
    p1, p2 = w.latch_lit(nL0), w.latch_lit(nL0 + 1)
    pool = [w.latch_lit(j) for j in range(nL0)] + [w.input_lit(i) for i in range(w.n_inputs)] + [0, 1]
    w.latches[nL0] = [rng.choice(pool) ^ rng.randint(0, 1), w.add_and(p2, p2 ^ 1)]
    w.latches[nL0 + 1] = [rng.choice(pool) ^ rng.randint(0, 1), p1]
    w.comments = ["d3 witness: p1 resets to (p2 AND NOT p2), p2 to p1"]
    return w


def any_literal(rng, c):
    pool = [0, 1] + [c.input_lit(i) for i in range(c.n_inputs)] + \
        [c.latch_lit(j) for j in range(len(c.latches))] + [a[0] for a in c.ands]
    return rng.choice(pool) ^ rng.randint(0, 1)


def mutate(c, op, rng, model):
    d = c.copy()
    if op == "and_input" and d.ands:
        i = rng.randrange(len(d.ands))
        lhs, a, b = d.ands[i]
        d.ands[i] = (lhs, a ^ 1, b) if rng.random() < 0.5 else (lhs, a, b ^ 1)
    elif op == "reset" and d.latches:
        j = rng.randrange(len(d.latches))
        d.latches[j][1] = any_literal(rng, d)
    elif op == "next" and d.latches:
        j = rng.randrange(len(d.latches))
        d.latches[j][0] = any_literal(rng, d)
    elif op == "constraint":
        if d.constraints and rng.random() < 0.5:
            d.constraints = d.constraints[1:]
        else:
            d.constraints = d.constraints + [any_literal(rng, d)]
    elif op == "bad":
        d.bad = [any_literal(rng, d)]
    elif op == "mapping" and model is not None:
        mL = len(model.latches)
        nL = min(mL, len(d.latches))
        perm = list(range(mL))
        rng.shuffle(perm)
        syms = ["i%d = %d" % (i, model.input_lit(i)) for i in range(min(d.n_inputs, model.n_inputs))]
        lat = [model.latch_lit(perm[j]) for j in range(nL)]
        x = rng.random()
        if x < 0.2 and nL:
            lat[0] ^= 1                                   # negated mapping
        elif x < 0.35 and nL and model.ands:
            lat[0] = rng.choice(model.ands)[0]            # gate mapping
        syms += ["l%d = %d" % (j, lat[j]) for j in range(nL)]
        d.symbols = syms
    elif op == "uninit" and d.latches:
        j = rng.randrange(len(d.latches))
        d.latches[j][1] = d.latch_lit(j)
    else:
        return None
    return d


def renumber_out_of_order(c, rng):
    """Swap the variable numbers of a gate and a later gate that reads it, so that the
    reader comes first. The circuit is unchanged; only the numbering is."""
    cand = [(a, b) for a in c.ands for b in c.ands
            if a[0] < b[0] and a[0] // 2 in (b[1] // 2, b[2] // 2)]
    if not cand:
        return None
    a, b = rng.choice(cand)
    va, vb = a[0] // 2, b[0] // 2

    def sw(x):
        v = x // 2
        if v == va:
            return 2 * vb + (x & 1)
        if v == vb:
            return 2 * va + (x & 1)
        return x

    d = c.copy()
    d.latches = [[sw(n), sw(r)] for n, r in c.latches]
    d.ands = [(sw(l), sw(r0), sw(r1)) for l, r0, r1 in c.ands]
    d.bad = [sw(x) for x in c.bad]
    d.constraints = [sw(x) for x in c.constraints]
    d.comments = c.comments + ["gate numbering permuted: gate %d now reads the later gate %d" % (2 * va, 2 * vb)]
    return d


class Writer:
    def __init__(self, out):
        self.out = out
        for sub in ("models", "witnesses"):
            os.makedirs(os.path.join(out, sub), exist_ok=True)
        path = os.path.join(out, "manifest.csv")
        new = not os.path.exists(path)
        self.f = open(path, "a", newline="")
        self.w = csv.writer(self.f)
        if new:
            self.w.writerow(["id", "family", "kind", "model", "witness", "base", "operator"])

    def model(self, name, c):
        p = os.path.join("models", name + ".aag")
        with open(os.path.join(self.out, p), "w") as f:
            f.write(c.to_aag())
        return p

    def witness(self, name, c):
        p = os.path.join("witnesses", name + ".aag")
        with open(os.path.join(self.out, p), "w") as f:
            f.write(c.to_aag())
        return p

    def row(self, *cols):
        self.w.writerow(cols)


def stage1(out, seed, n_models):
    rng = random.Random(seed)
    W = Writer(out)
    bases = []
    for i in range(n_models):
        kind = "std" if i % 2 == 0 else "ext"
        m = random_model(rng, kind)
        mid = "m%04d" % i
        m.comments = ["%s model %d, seed %d" % (kind, i, seed)]
        mp = W.model(mid, m)
        ex = exact_witness(m, rng)
        if ex is None:
            continue
        for fam, w in (("exact", ex), ("aux", aux_witness(m, ex, rng)),
                       ("kp", aux_witness(m, ex, rng, kp=True)),
                       ("d1", d1_witness(m, ex, rng)), ("d3", d3_witness(m, ex, rng))):
            if w is None:
                continue
            wid = "%s_%s" % (mid, fam)
            wp = W.witness(wid, w)
            W.row(wid, fam, kind, mp, wp, "", "")
            bases.append((wid, kind, m, mp, w))
    mutants(W, rng, bases)
    W.f.close()


def mutants(W, rng, bases):
    for wid, kind, m, mp, w in bases:
        for k in range(3):
            op = rng.choice(OPERATORS)
            d = mutate(w, op, rng, m)
            if d is None:
                continue
            mid = "%s_mut%d" % (wid, k)
            W.row(mid, "mut", kind, mp, W.witness(mid, d), wid, op)
        op = rng.choice(["and_input", "reset", "next", "constraint", "bad"])
        mm = mutate(m, op, rng, None)
        if mm is not None:
            mid = "%s_mmut" % wid
            W.row(mid, "mmut", kind, W.model(mid, mm), os.path.relpath(
                os.path.join(W.out, "witnesses", wid + ".aag"), W.out), wid, op)
        o = renumber_out_of_order(w, rng)
        if o is not None and rng.random() < 0.25:
            oid = "%s_order" % wid
            W.row(oid, "order", kind, mp, W.witness(oid, o), wid, "renumber")


def stage3(out, seed):
    rng = random.Random(seed + 3)
    W = Writer(out)
    d = os.path.join(out, "ric3")
    bases = []
    for name in sorted(os.listdir(d)) if os.path.isdir(d) else []:
        if not name.endswith(".cert.aag"):
            continue
        mid = name[:-len(".cert.aag")]
        mp = os.path.join("models", mid + ".aag")
        with open(os.path.join(out, mp)) as f:
            m = from_aag(f.read())
        with open(os.path.join(d, name)) as f:
            w = from_aag(f.read())
        wid = "%s_ric3" % mid
        wp = W.witness(wid, w)
        W.row(wid, "ric3", "std", mp, wp, "", "")
        bases.append((wid, "std", m, mp, w))
    mutants(W, rng, bases)
    W.f.close()


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("stage", choices=["stage1", "stage3"])
    ap.add_argument("out")
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--models", type=int, default=400)
    a = ap.parse_args(argv)
    if a.stage == "stage1":
        stage1(a.out, a.seed, a.models)
    else:
        stage3(a.out, a.seed)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
