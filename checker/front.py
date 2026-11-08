#!/usr/bin/env python3
"""AIGER front end of the reference checker.

    front.py MODEL WITNESS [--budget E]

Reads a model and a witness circuit (ASCII or binary AIGER, with Certifaiger's
extension that a latch may reset to any literal), reproduces the way Certifaiger
reads the shared-literal mapping, and either prints the JSON input of `kcheck`
(exit 0) or a refusal with its reason (exit 2).

What is reproduced from Certifaiger (src/certifaiger.cpp at commit ba86b456):
  * both files must be "reencoded": inputs are literals 2, 4, ..., then latches;
  * the mapping comes from a comment line "MAPPING n" followed by n lines
    "<witness literal> <model literal>"; else from witness input and latch symbols
    containing '=' (the number after '=' is the model literal); else the default,
    which pairs the first inputs and the first latches in order;
  * the property is the conjunction of the negated bad literals, and the negated
    outputs when the file has neither bad nor justice literals.

What is refused (outside the mechanized model): negated, gate, constant and
input-latch mappings; mappings that are not injective; liveness (justice or
fairness); gates that read a later or undefined variable; and pairs whose
enumeration would exceed the budget. A malformed MAPPING comment is refused too,
since Certifaiger's handling of it depends on how the tool was built.

This file is trusted: the checker's soundness theorem covers the circuits this front
end hands to kcheck, not the file on disk.
"""
import json
import sys

WS = " \f\n\r\t\v"


class Aiger:
    def __init__(self):
        self.maxvar = 0
        self.inputs = []
        self.latches = []        # (lit, next, reset)
        self.outputs = []
        self.bad = []
        self.constraints = []
        self.justice = []        # list of lists
        self.fairness = []
        self.ands = []           # (lhs, rhs0, rhs1)
        self.symbols = {}        # (kind, position) -> name
        self.comments = []
        self.binary = False


class AigerError(Exception):
    pass


def _nums(line, n_min, n_max, what):
    toks = line.split()
    if not (n_min <= len(toks) <= n_max) or not all(t.isdigit() for t in toks):
        raise AigerError("bad %s line: %r" % (what, line))
    return [int(t) for t in toks]


def read_aiger(path):
    with open(path, "rb") as f:
        data = f.read()
    a = Aiger()
    pos = 0

    def line():
        nonlocal pos
        end = data.find(b"\n", pos)
        if end < 0:
            end = len(data)
        s = data[pos:end].decode("ascii", "replace")
        pos = end + 1
        return s

    header = line().split()
    if not header or header[0] not in ("aag", "aig"):
        raise AigerError("no AIGER header")
    a.binary = header[0] == "aig"
    counts = [int(t) for t in header[1:]]
    if not 5 <= len(counts) <= 9:
        raise AigerError("bad header")
    counts += [0] * (9 - len(counts))
    M, I, L, O, A, B, C, J, F = counts
    a.maxvar = M
    if a.binary:
        a.inputs = [2 * (i + 1) for i in range(I)]
    else:
        a.inputs = [_nums(line(), 1, 1, "input")[0] for _ in range(I)]
    for i in range(L):
        if a.binary:
            v = _nums(line(), 1, 2, "latch")
            lit = 2 * (I + i + 1)
        else:
            v = _nums(line(), 2, 3, "latch")
            lit, v = v[0], v[1:]
        a.latches.append((lit, v[0], v[1] if len(v) > 1 else 0))
    a.outputs = [_nums(line(), 1, 1, "output")[0] for _ in range(O)]
    a.bad = [_nums(line(), 1, 1, "bad")[0] for _ in range(B)]
    a.constraints = [_nums(line(), 1, 1, "constraint")[0] for _ in range(C)]
    sizes = [_nums(line(), 1, 1, "justice size")[0] for _ in range(J)]
    a.justice = [[_nums(line(), 1, 1, "justice")[0] for _ in range(s)] for s in sizes]
    a.fairness = [_nums(line(), 1, 1, "fairness")[0] for _ in range(F)]
    if a.binary:
        def varint():
            nonlocal pos
            x, shift = 0, 0
            while True:
                if pos >= len(data):
                    raise AigerError("truncated binary gate section")
                byte = data[pos]
                pos += 1
                x |= (byte & 0x7F) << shift
                if not byte & 0x80:
                    return x
                shift += 7
        for i in range(A):
            lhs = 2 * (I + L + i + 1)
            r0 = lhs - varint()
            r1 = r0 - varint()
            a.ands.append((lhs, r0, r1))
    else:
        a.ands = [tuple(_nums(line(), 3, 3, "and")) for _ in range(A)]
    while pos < len(data):
        s = line()
        if s == "c":
            rest = data[pos:].decode("ascii", "replace").split("\n")
            if rest and rest[-1] == "":
                rest.pop()
            a.comments = rest
            break
        if not s:
            continue
        kind = s[0]
        sp = s.find(" ")
        if kind in "ilobcjf" and sp > 1 and s[1:sp].isdigit():
            a.symbols[(kind, int(s[1:sp]))] = s[sp + 1:]
    return a


def reencoded(a):
    lits = a.inputs + [l[0] for l in a.latches]
    return lits == [2 * (i + 1) for i in range(len(lits))]


def parse_num(c):
    """std::from_chars as Certifaiger calls it: skip leading whitespace, read digits."""
    i = 0
    while i < len(c) and c[i] in WS:
        i += 1
    if i == len(c):
        return None
    j = i
    while j < len(c) and c[j].isdigit():
        j += 1
    if j == i:
        return None
    return int(c[i:j]), c[j:]


class MalformedMapping(Exception):
    pass


def _mapping_comment(w, keyword):
    for k, c in enumerate(w.comments):
        if not c.startswith(keyword):
            continue
        n = parse_num(c[len(keyword):])
        if n is None:
            raise MalformedMapping("mapping comment without a count")
        n = n[0]
        lines = w.comments[k + 1:k + 1 + n]
        if len(lines) < n:
            raise MalformedMapping("incomplete mapping comment")
        out = []
        for ln in lines:
            a = parse_num(ln)
            b = parse_num(a[1]) if a else None
            if b is None:
                raise MalformedMapping("unreadable mapping line")
            out.append((a[0], b[0]))
        return out
    return None


def _mapping_symbols(w, symbol):
    nI = len(w.inputs)
    out = []
    for i in range(nI + len(w.latches)):
        name = w.symbols.get(("i", i)) if i < nI else w.symbols.get(("l", i - nI))
        if name is None or symbol not in name:
            continue
        lit = parse_num(name[name.find(symbol) + 1:])
        if lit is None:
            continue
        out.append((2 * (i + 1), lit[0]))
    return out or None


def certifaiger_mapping(m, w):
    """The shared pairs (witness literal, model literal), and where they came from."""
    pairs = _mapping_comment(w, "MAPPING ")
    if pairs is not None:
        return pairs, "MAPPING"
    pairs = _mapping_symbols(w, "=")
    if pairs is not None:
        return pairs, "symbols"
    nI = min(len(m.inputs), len(w.inputs))
    nL = min(len(m.latches), len(w.latches))
    pairs = [(w.inputs[i], m.inputs[i]) for i in range(nI)]
    pairs += [(w.latches[i][0], m.latches[i][0]) for i in range(nL)]
    return pairs, "default"


def _kind(a, lit):
    v = lit // 2
    if v == 0:
        return "constant", None
    if 1 <= v <= len(a.inputs):
        return "input", v - 1
    if len(a.inputs) < v <= len(a.inputs) + len(a.latches):
        return "latch", v - 1 - len(a.inputs)
    if any(g[0] // 2 == v for g in a.ands):
        return "gate", None
    return "undefined", None


def classify(m, w, pairs):
    """(True, interface) when the pairs fit the mechanized model, else (False, reason)."""
    if m.justice or m.fairness or w.justice or w.fairness:
        return False, "liveness"
    lp, ip = [], []
    for wl, ml in pairs:
        if wl % 2 or ml % 2:
            return False, "negated mapping"
        wk, wi = _kind(w, wl)
        mk, mi = _kind(m, ml)
        if "undefined" in (wk, mk):
            return False, "mapping names an undefined literal"
        if "gate" in (wk, mk):
            return False, "gate mapping"
        if "constant" in (wk, mk):
            return False, "constant mapping"
        if wk != mk:
            return False, "input-latch mapping"
        (lp if wk == "latch" else ip).append([wi, mi])
    for side in (lp, ip):
        for k in (0, 1):
            vals = [p[k] for p in side]
            if len(set(vals)) != len(vals):
                return False, "non-injective mapping"
    return True, {"latchPairs": lp, "inputPairs": ip}


def gate_order_problem(a):
    """None when every gate reads only constants, inputs, latches and earlier gates."""
    defined = set(range(len(a.inputs) + len(a.latches) + 1))
    for lhs, r0, r1 in sorted(a.ands):
        if lhs % 2 or lhs // 2 in defined or lhs // 2 > a.maxvar:
            return "gate %d redefines a variable" % lhs
        if r0 // 2 not in defined or r1 // 2 not in defined:
            return "gate %d reads a later or undefined variable" % lhs
        defined.add(lhs // 2)
    used = [l[1] for l in a.latches] + [l[2] for l in a.latches]
    used += a.outputs + a.bad + a.constraints
    for lit in used:
        if lit // 2 not in defined:
            return "literal %d is undefined" % lit
    return None


def to_graph(a):
    bad = a.bad if a.bad else ([] if a.justice else list(a.outputs))
    return {
        "nI": len(a.inputs),
        "nL": len(a.latches),
        "maxVar": a.maxvar,
        "latchNext": [l[1] for l in a.latches],
        "latchReset": [l[2] for l in a.latches],
        "ands": [list(g) for g in sorted(a.ands)],
        "bad": bad,
        "cons": list(a.constraints),
    }


def budget_exponent(m, w):
    """log2 of the number of cheap steps in the costliest check (the transition check)."""
    return 2 * len(m.inputs) + len(m.latches) + len(w.latches) + 2 * len(w.inputs)


def refuse(reason):
    print(json.dumps({"verdict": "refused", "reason": reason}))
    return 2


def main(argv):
    args = [x for x in argv if not x.startswith("--")]
    budget = 24
    for x in argv:
        if x.startswith("--budget="):
            budget = int(x.split("=", 1)[1])
    if len(args) != 2:
        print("usage: front.py MODEL WITNESS [--budget=E]", file=sys.stderr)
        return 2
    try:
        m, w = read_aiger(args[0]), read_aiger(args[1])
    except (OSError, AigerError, ValueError) as e:
        return refuse("malformed AIGER: %s" % e)
    for name, a in (("model", m), ("witness", w)):
        if not reencoded(a):
            return refuse("%s not reencoded" % name)
    try:
        pairs, source = certifaiger_mapping(m, w)
    except MalformedMapping as e:
        return refuse("malformed MAPPING comment: %s" % e)
    ok, info = classify(m, w, pairs)
    if not ok:
        return refuse(info)
    for name, a in (("model", m), ("witness", w)):
        problem = gate_order_problem(a)
        if problem:
            return refuse("%s: %s" % (name, problem))
    e = budget_exponent(m, w)
    if e > budget:
        return refuse("enumeration budget exceeded (2^%d steps, budget 2^%d)" % (e, budget))
    out = {"model": to_graph(m), "witness": to_graph(w), "mappingSource": source}
    out.update(info)
    print(json.dumps(out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
