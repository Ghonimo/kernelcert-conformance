"""Tests for front.py, the AIGER front end of the reference checker.

Run:  python3 -I test_front.py   (exit 0 when every test passes)
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import front  # noqa: E402

FIX = os.path.join(HERE, "..", "study", "corpus", "certifaiger_tests")
failures = []


def check(name, cond):
    if not cond:
        failures.append(name)
    print(("ok   " if cond else "FAIL ") + name)


def write(text, binary=False):
    f = tempfile.NamedTemporaryFile("wb", suffix=".aig" if binary else ".aag", delete=False)
    f.write(text if binary else text.encode())
    f.close()
    return f.name


# 1. ASCII parsing: header, latch resets (default 0), outputs, bad, constraints, symbols, comments
a = front.read_aiger(write("aag 4 1 2 1 1 1 1\n2\n4 8\n6 7 3\n8\n6\n2\n8 4 2\ni0 req\nl1 = 6\nc\nhello\n"))
check("ascii counts", (a.maxvar, len(a.inputs), len(a.latches), len(a.ands)) == (4, 1, 2, 1))
check("ascii latch reset default 0", a.latches[0] == (4, 8, 0))
check("ascii latch explicit reset", a.latches[1] == (6, 7, 3))
check("ascii outputs/bad/constraints", (a.outputs, a.bad, a.constraints) == ([8], [6], [2]))
check("ascii symbols", a.symbols.get(("i", 0)) == "req" and a.symbols.get(("l", 1)) == "= 6")
check("ascii comments", a.comments == ["hello"])

# 2. Binary parsing equals the ASCII reading of the same circuit (and gate 6 = 4 & 2)
b = front.read_aiger(write(b"aig 3 1 1 1 1\n6\n6\n\x02\x02", binary=True))
c = front.read_aiger(write("aag 3 1 1 1 1\n2\n4 6\n6\n6 4 2\n"))
check("binary equals ascii", (b.inputs, b.latches, b.outputs, b.ands) == (c.inputs, c.latches, c.outputs, c.ands))

# 3. Mapping: '=' symbols, the MAPPING comment, and the default, as Certifaiger reads them
m = front.read_aiger(write("aag 2 1 1 0 0\n2\n4 4\n"))
w_sym = front.read_aiger(write("aag 2 1 1 0 0\n2\n4 4\ni0 = 2\nl0 =  4\n"))
pairs, src = front.certifaiger_mapping(m, w_sym)
check("symbol mapping", (pairs, src) == ([(2, 2), (4, 4)], "symbols"))
w_cmt = front.read_aiger(write("aag 2 1 1 0 0\n2\n4 4\nc\nMAPPING 1\n4 4\n"))
pairs, src = front.certifaiger_mapping(m, w_cmt)
check("comment mapping wins", (pairs, src) == ([(4, 4)], "MAPPING"))
w_def = front.read_aiger(write("aag 2 1 1 0 0\n2\n4 4\n"))
pairs, src = front.certifaiger_mapping(m, w_def)
check("default mapping", (pairs, src) == ([(2, 2), (4, 4)], "default"))
w_comb = front.read_aiger(write("aag 1 0 1 0 0\n2 2\nl0 = 4 < 2\n"))
m2 = front.read_aiger(write("aag 2 0 2 0 0 1\n2 2 1\n4 4\n4\n"))
check("'=' then '<' in one symbol", front.certifaiger_mapping(m2, w_comb)[0] == [(2, 4)])

# 4. Scope: what the mechanized model covers, and the reasons for refusing the rest
ok, info = front.classify(m, w_sym, [(2, 2), (4, 4)])
check("in scope: input and latch pairs", ok and info == {"latchPairs": [[0, 0]], "inputPairs": [[0, 0]]})
check("refuse negated mapping", front.classify(m, w_sym, [(4, 5)]) == (False, "negated mapping"))
check("refuse gate mapping", front.classify(m, front.read_aiger(write("aag 3 1 1 0 1\n2\n4 4\n6 4 2\n")), [(6, 4)]) == (False, "gate mapping"))
check("refuse input-latch mapping", front.classify(m, w_sym, [(2, 4)]) == (False, "input-latch mapping"))
check("refuse non-injective mapping", front.classify(m, w_sym, [(2, 2), (4, 2)])[0] is False)
live = front.read_aiger(write("aag 2 1 1 0 0 0 0 1 0\n2\n4 4\n1\n4\n"))
check("refuse liveness", front.classify(live, w_sym, [(2, 2)]) == (False, "liveness"))

# 5. Graph export: outputs act as bad when there is no bad and no justice; gate order checked
g = front.to_graph(front.read_aiger(write("aag 3 1 1 1 1\n2\n4 6\n7\n6 4 2\n")))
check("outputs as bad", g["bad"] == [7] and g["ands"] == [[6, 4, 2]] and g["latchReset"] == [0])
unordered = front.read_aiger(write("aag 4 1 1 0 2\n2\n4 8\n8 6 2\n6 4 2\n"))
check("gates sorted by index", front.to_graph(unordered)["ands"] == [[6, 4, 2], [8, 6, 2]])
backward = front.read_aiger(write("aag 4 1 1 0 2\n2\n4 6\n6 8 2\n8 4 2\n"))
check("refuse gate reading a later gate", front.gate_order_problem(backward) is not None)

# 6. Certifaiger's own tests: in scope or refused for the documented reason
def run(model, witness):
    p = subprocess.run([sys.executable, "-I", os.path.join(HERE, "front.py"),
                        os.path.join(FIX, model), os.path.join(FIX, witness)],
                       capture_output=True, text=True)
    return p.returncode, json.loads(p.stdout)


rc, out = run("01_model.aag", "01_witness.aag")
check("01 in scope", rc == 0 and out["latchPairs"] == [[0, 0], [1, 1], [2, 2], [3, 3]])
rc, out = run("map_gate_model.aag", "map_gate_witness.aag")
check("map_gate refused: gate mapping", rc == 2 and out["reason"] == "gate mapping")
rc, out = run("latch_to_input_model.aag", "latch_to_input_witness.aag")
check("latch_to_input refused: input-latch mapping", rc == 2 and out["reason"] == "input-latch mapping")
rc, out = run("negated_reset_model.aag", "negated_reset_witness.aag")
check("negated_reset in scope", rc == 0)
rc, out = run("stress_model.aig", "stress_witness.aig")
check("stress refused: enumeration budget", rc == 2 and out["reason"].startswith("enumeration budget"))

print("%d failure(s)" % len(failures))
sys.exit(1 if failures else 0)
