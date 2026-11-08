# Findings about third-party tools

## F1. Certifaiger: ASCII witnesses whose gates read a later-numbered gate

**Claim.** On a valid ASCII AIGER witness in which an AND gate reads a gate with a higher
variable number, Certifaiger's release builds grow to several gigabytes and end without a
verdict (killed by its own memory cap, or a segmentation fault without one), and its build
with assertions fails `Assertion 'map[c][t][a->rhs1] != INVALID_LIT'` in `unroll`. It never
accepts such a witness. Renumbering the gates (converting the file to binary AIGER, which
orders them) restores the verdict the same witness gets with ordered gates.

**Confirmation before the counted run (2026-11-04, on the study host).**
1. Source pinned: Certifaiger `ba86b456`; `src/certifaiger.cpp` SHA-256
   `e8306292c9ed8af64b9d5f87bff392a4e62ee7f78c34fb3895b441e9a6c858e6`.
2. Second tool: the AIGER library's `aigtoaig` reads the file and writes it as binary
   (exit 0), so the file is well formed for the format's reference implementation.
3. Differential control, pilot pair `m0003_exact_order` (base `m0003_exact`):
   original witness: release build exit 1 (`certifaiger failed with exit code 137`, its
   `SPACE=2048` cap), assertion build fails the assertion above; the same witness renumbered
   by `aigtoaig`: both builds print `valid witness`; the base witness: `valid witness`.
4. Documentation: the AIGER format description says that in the ASCII format "the order of
   the literals and the definitions of the AND gates is irrelevant" (FORMAT, commit
   039ec1a2cc). Certifaiger's README requires consecutive indexing of inputs and latches
   (checked by `reencoded()`); it does not mention the order of gates, and nothing checks it.
   `unroll` visits literals in increasing order and assumes both inputs of a gate are
   already mapped.
5. Scope: the format allows the file; HWMCC distributes binary AIGER, where the order is
   enforced, so competition witnesses are not affected.
6. Wording used in the paper: "Certifaiger assumes, without checking, that every gate of an ASCII
   witness reads only lower-numbered variables. Valid ASCII witnesses that break this
   assumption make its release builds exhaust memory or crash and its assertion build stop
   on an assertion; none was accepted. Renumbering the gates restores the expected verdict."
7. Security: none (a crash, never an acceptance). No coordinated disclosure needed; the
   maintainers are told before publication.

**Counted run** (`study/results/`, family `order`, 343 renumbered copies of generated
witnesses; every verdict compared with the same witness before renumbering):

| Build | ordered witness accepted (229) | ordered witness rejected (114) |
|---|---|---|
| current, release | 229 killed at the 4,096 MB cap (exit 137, within 4 s) | 27 killed, 87 rejected |
| current, assertions on | 229 assertion failures in `unroll` | 27 assertion failures, 87 rejected |
| 10.2.1, release | 136 killed (93 rejected as not stratified) | 22 killed, 92 rejected |

No build accepted a renumbered witness, and every verdict a build gave on one equals its
verdict on the ordered witness. Post hoc, all 343 renumbered witnesses converted to binary
by `aigtoaig` get their ordered original's verdict from the release build (229 accept,
114 reject; `results/posthoc_order_binary.csv`). The tested build is Certifaiger 10.4.0
(`ba86b456`), whose checker source equals 10.3.0's. The assertion that fails is `map[c][t][a->rhs0] !=
INVALID_LIT` in 170 calls and the `rhs1` form in 86. The reference checker refuses all
343 (gate order), as pre-registered (E2).

**Certifaiger 10.4.1** (`b540f0c5`, released 2026-11-05, after the counted run; post hoc,
`results/posthoc_cf1041.csv`). Its release build gave all 343 renumbered witnesses the
outcome of 10.4.0: 256 killed at the 4,096 MB cap (exit 137), 87 rejected, none accepted.
Its source changes only the padding of liveness signals, a check name and comments, so the
defect is present in the latest release. Smallest case in the corpus: `m0048_ric3_order`,
a copy of the rIC3 certificate `m0048_ric3` (accepted) with its gates renumbered so that
gate 6 reads gate 8 (killed after 2.7 s).

**Maintainers.** Told on 2026-11-07 in Certifaiger's issue tracker:
https://github.com/Froleyks/certifaiger/issues/10 (this finding) and
https://github.com/Froleyks/certifaiger/issues/11 (whether the differences D1 and D3 are
intended). Their answers will be recorded here.
