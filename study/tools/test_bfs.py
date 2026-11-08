"""Tests for bfs.py, the explicit-state ground truth.  Run: python3 -I test_bfs.py"""
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bfs  # noqa: E402

fails = []


def case(name, aag, expect):
    f = tempfile.NamedTemporaryFile("w", suffix=".aag", delete=False)
    f.write(aag)
    f.close()
    got = bfs.check_file(f.name)
    ok = got[0] == expect[0] and (len(expect) < 2 or got[1] == expect[1])
    print(("ok   " if ok else "FAIL ") + name + "  " + repr(got))
    if not ok:
        fails.append(name)


# a latch that stays low (reset 0, next = itself), bad = latch: safe
case("hold low", "aag 1 0 1 0 0 1\n2 2\n2\n", ("safe",))
# toggling latch: high at time 1
case("toggle", "aag 1 0 1 0 0 1\n2 3\n2\n", ("unsafe", 1))
# reset high: bad at time 0
case("reset high", "aag 1 0 1 0 0 1\n2 2 1\n2\n", ("unsafe", 0))
# uninitialized latch (reset = itself): either value at time 0
case("uninitialized", "aag 1 0 1 0 0 1\n2 2 2\n2\n", ("unsafe", 0))
# reset reads an input: latch takes the input at time 0, so it can start high
case("reset reads input", "aag 2 1 1 0 0 1\n2\n4 4 2\n4\n", ("unsafe", 0))
# a constraint forbids the input that would raise the latch: safe
case("constraint blocks", "aag 2 1 1 0 0 1 1\n2\n4 2\n4\n3\n", ("safe",))
# without the constraint the input raises it at time 1
case("no constraint", "aag 2 1 1 0 0 1\n2\n4 2\n4\n", ("unsafe", 1))
# old AIGER: output is the bad signal when there is no bad section
case("output as bad", "aag 1 0 1 1 0\n2 3\n2\n", ("unsafe", 1))
# reset to another latch: l2 resets to l1, l1 resets low; bad = l2: safe while both hold
case("reset to latch", "aag 2 0 2 0 0 1\n2 2 0\n4 4 2\n4\n", ("safe",))
# a reset equation with no solution (latch resets to its own negation): no initial state, safe
case("no reset state", "aag 1 0 1 0 0 1\n2 2 3\n3\n", ("safe",))
# AND gate: bad when both latches high; they rise at times 1 and 2 respectively
case("and gate", "aag 3 0 2 0 1 1\n2 1\n4 2\n6\n6 4 2\n", ("unsafe", 2))
print("%d failure(s)" % len(fails))
sys.exit(1 if fails else 0)
