"""Small ASCII AIGER circuits for the corpus generator: build, read, write, evaluate.

Only the generator uses this module. The checker's front end (checker/front.py) and the
ground truth (study/tools/bfs.py) each have their own reader.
"""
import itertools


class Circuit:
    """A reencoded ASCII AIGER 1.9 circuit: inputs are variables 1..I, latches follow,
    AND gates after them. Latches are (next, reset) pairs of literals."""

    def __init__(self, n_inputs=0):
        self.n_inputs = n_inputs
        self.latches = []          # [next, reset] per latch
        self.ands = []             # (lhs, rhs0, rhs1)
        self.bad = []
        self.constraints = []
        self.symbols = []          # lines such as "l0 = 4"
        self.comments = []
        self._next_var = None

    # literals
    def input_lit(self, i):
        return 2 * (i + 1)

    def latch_lit(self, j):
        return 2 * (self.n_inputs + j + 1)

    def maxvar(self):
        top = self.n_inputs + len(self.latches)
        if self.ands:
            top = max(top, max(a[0] // 2 for a in self.ands))
        return top

    def add_latch(self, nxt=0, reset=0):
        if self.ands:
            raise ValueError("add latches before gates")
        self.latches.append([nxt, reset])
        return self.latch_lit(len(self.latches) - 1)

    def add_and(self, a, b):
        lhs = 2 * (self.maxvar() + 1)
        self.ands.append((lhs, a, b))
        return lhs

    def add_or(self, a, b):
        return self.add_and(a ^ 1, b ^ 1) ^ 1

    def add_and_all(self, lits):
        if not lits:
            return 1
        acc = lits[0]
        for x in lits[1:]:
            acc = self.add_and(acc, x)
        return acc

    def add_or_all(self, lits):
        if not lits:
            return 0
        acc = lits[0]
        for x in lits[1:]:
            acc = self.add_or(acc, x)
        return acc

    # text
    def to_aag(self):
        I, L, A = self.n_inputs, len(self.latches), len(self.ands)
        head = "aag %d %d %d 0 %d %d %d" % (self.maxvar(), I, L, A, len(self.bad), len(self.constraints))
        out = [head]
        out += [str(self.input_lit(i)) for i in range(I)]
        for j, (nxt, rst) in enumerate(self.latches):
            out.append("%d %d %d" % (self.latch_lit(j), nxt, rst))
        out += [str(b) for b in self.bad]
        out += [str(c) for c in self.constraints]
        out += ["%d %d %d" % g for g in self.ands]
        out += self.symbols
        if self.comments:
            out.append("c")
            out += self.comments
        return "\n".join(out) + "\n"

    def copy(self):
        c = Circuit(self.n_inputs)
        c.latches = [list(l) for l in self.latches]
        c.ands = list(self.ands)
        c.bad = list(self.bad)
        c.constraints = list(self.constraints)
        c.symbols = list(self.symbols)
        c.comments = list(self.comments)
        return c


def from_aag(text):
    lines = text.split("\n")
    h = lines[0].split()
    cnt = [int(x) for x in h[1:]] + [0] * 9
    M, I, L, O, A, B, C = cnt[:7]
    c = Circuit(I)
    k = 1 + I
    for j in range(L):
        t = [int(x) for x in lines[k + j].split()]
        c.latches.append([t[1], t[2] if len(t) > 2 else 0])
    k += L
    outs = [int(lines[k + j]) for j in range(O)]
    k += O
    c.bad = [int(lines[k + j]) for j in range(B)]
    k += B
    c.constraints = [int(lines[k + j]) for j in range(C)]
    k += C
    c.ands = [tuple(int(x) for x in lines[k + j].split()) for j in range(A)]
    k += A
    if not c.bad:
        c.bad = outs
    rest = lines[k:]
    if "c" in rest:
        i = rest.index("c")
        c.symbols = [s for s in rest[:i] if s]
        c.comments = [s for s in rest[i + 1:] if s]
    else:
        c.symbols = [s for s in rest if s]
    return c


def evaluate(c, inputs, state):
    """Variable values (index = variable) for input and latch bit tuples."""
    val = [False] * (c.maxvar() + 1)
    for i, b in enumerate(inputs):
        val[i + 1] = b
    for j, b in enumerate(state):
        val[c.n_inputs + j + 1] = b
    for lhs, r0, r1 in sorted(c.ands):
        val[lhs // 2] = (val[r0 // 2] ^ bool(r0 & 1)) and (val[r1 // 2] ^ bool(r1 & 1))
    return val


def lit(val, x):
    return val[x // 2] ^ bool(x & 1)


def reach_overapprox(c):
    """States reachable when every state in the set may take any constrained input:
    the initial states (reset fixpoints whose constraints hold) closed under
    constrained steps. Also whether a constrained bad configuration occurs in it."""
    nI, nL = c.n_inputs, len(c.latches)
    ins = list(itertools.product([False, True], repeat=nI))
    states = list(itertools.product([False, True], repeat=nL))
    seen, frontier, bad = set(), [], False
    for s in states:
        for i in ins:
            v = evaluate(c, i, s)
            if not all(lit(v, x) for x in c.constraints):
                continue
            if all(s[j] == lit(v, c.latches[j][1]) for j in range(nL)) and s not in seen:
                seen.add(s)
                frontier.append(s)
    while frontier:
        s = frontier.pop()
        for i in ins:
            v = evaluate(c, i, s)
            if not all(lit(v, x) for x in c.constraints):
                continue
            if any(lit(v, b) for b in c.bad):
                bad = True
            t = tuple(lit(v, c.latches[j][0]) for j in range(nL))
            if t not in seen:
                seen.add(t)
                frontier.append(t)
    return seen, bad
