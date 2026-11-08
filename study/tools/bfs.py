#!/usr/bin/env python3
"""Explicit-state ground truth for small AIGER models.

    bfs.py MODEL.aag      prints "safe" or "unsafe <depth>"; exit 0 / 1, 2 on error

Semantics, the same as the paper's `Safe`:
  * a configuration is a latch state with an input valuation;
  * it is initial when every latch equals its reset literal evaluated at that very
    configuration (a latch whose reset literal is itself is unconstrained; resets may
    read inputs, latches and gates) and every constraint holds;
  * from a configuration whose constraints hold, the successor state is given by the
    next-state literals, and every input valuation whose constraints hold there gives
    a successor configuration;
  * the model is unsafe when some reachable configuration whose constraints hold sets
    a bad literal (the outputs, when there are no bad and no justice literals).

This file has its own reader and shares no code with the checker's front end, so that
the ground truth is an independent path. ASCII AIGER only (convert binary files with
aigtoaig first).
"""
import sys


def parse(path):
    with open(path) as f:
        lines = f.read().split("\n")
    head = lines[0].split()
    if not head or head[0] != "aag":
        raise ValueError("ASCII AIGER expected")
    cnt = [int(x) for x in head[1:]] + [0] * 9
    M, I, L, O, A, B, C, J, F = cnt[:9]
    k = 1
    inputs = [int(lines[k + i]) for i in range(I)]
    k += I
    latches = []
    for i in range(L):
        t = [int(x) for x in lines[k + i].split()]
        latches.append((t[0], t[1], t[2] if len(t) > 2 else 0))
    k += L
    outputs = [int(lines[k + i]) for i in range(O)]
    k += O
    bad = [int(lines[k + i]) for i in range(B)]
    k += B
    cons = [int(lines[k + i]) for i in range(C)]
    k += C
    jsizes = [int(lines[k + i]) for i in range(J)]
    k += J + sum(jsizes) + F
    ands = [tuple(int(x) for x in lines[k + i].split()) for i in range(A)]
    if not bad and not J:
        bad = outputs
    return M, inputs, latches, ands, bad, cons


def compile_order(ands):
    """Gates in an order where each reads only earlier variables."""
    by = {g[0] // 2: g for g in ands}
    order, state = [], {}

    def visit(v):
        if v not in by or state.get(v) == 2:
            return
        if state.get(v) == 1:
            raise ValueError("combinational cycle")
        state[v] = 1
        _, r0, r1 = by[v]
        visit(r0 // 2)
        visit(r1 // 2)
        state[v] = 2
        order.append(by[v])

    for v in sorted(by):
        visit(v)
    return order


def check_file(path):
    M, inputs, latches, ands, bad, cons = parse(path)
    order = compile_order(ands)
    nI, nL = len(inputs), len(latches)
    in_vars = [l // 2 for l in inputs]
    lat_vars = [l[0] // 2 for l in latches]

    def evaluate(s, i):
        val = [False] * (M + 1)
        for b, v in enumerate(in_vars):
            val[v] = bool((i >> b) & 1)
        for b, v in enumerate(lat_vars):
            val[v] = bool((s >> b) & 1)
        for lhs, r0, r1 in order:
            val[lhs // 2] = (val[r0 // 2] ^ (r0 & 1 == 1)) and (val[r1 // 2] ^ (r1 & 1 == 1))
        return val

    def lit(val, x):
        return val[x // 2] ^ (x & 1 == 1)

    def successor(val):
        s = 0
        for b, (_, nxt, _) in enumerate(latches):
            if lit(val, nxt):
                s |= 1 << b
        return s

    frontier = set()
    for s in range(1 << nL):
        for i in range(1 << nI):
            val = evaluate(s, i)
            if not all(lit(val, c) for c in cons):
                continue
            if not all(bool((s >> b) & 1) == lit(val, latches[b][2]) for b in range(nL)):
                continue
            if any(lit(val, b) for b in bad):
                return ("unsafe", 0)
            frontier.add(successor(val))
    seen = set(frontier)
    depth = 1
    while frontier:
        nxt = set()
        for s in frontier:
            for i in range(1 << nI):
                val = evaluate(s, i)
                if not all(lit(val, c) for c in cons):
                    continue
                if any(lit(val, b) for b in bad):
                    return ("unsafe", depth)
                t = successor(val)
                if t not in seen:
                    seen.add(t)
                    nxt.add(t)
        frontier = nxt
        depth += 1
    return ("safe",)


def main(argv):
    if len(argv) != 1:
        print("usage: bfs.py MODEL.aag", file=sys.stderr)
        return 2
    try:
        r = check_file(argv[0])
    except (OSError, ValueError, IndexError) as e:
        print("error: %s" % e)
        return 2
    print(" ".join(str(x) for x in r))
    return 0 if r[0] == "safe" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
