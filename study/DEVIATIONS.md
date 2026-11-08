# Deviations from PREREGISTRATION.md

## D1 (2026-11-04, 12:55): counted run restarted with Certifaiger's own resource caps

The first counted run (started 12:47:27 from commit 8f7d7e5) was stopped by hand after
about 2,960 of 7,613 pairs. On witnesses of the `order` family (gates numbered out of
order, valid ASCII AIGER) the release builds of Certifaiger grew to 7 to 12 GB per
process within 20 s; with up to four such calls running at once, the shared host
(62 GB) was down to 4 GB free. The harness, and only it, was stopped.

Change: every Certifaiger call now runs with Certifaiger's own `limit` caps, `TIME=120`
seconds and `SPACE=4096` MB; a call that hits a cap is recorded with verdict `limit`,
not as a rejection. Jobs reduced from 16 to 12. Nothing else changed: same corpus seed,
generator, tools and analysis. The partial results of the stopped run are kept, unused,
in `counted_aborted_1/` on the host.

Effect on the predictions: none by construction (a capped call is neither an accept nor
a reject); the memory growth itself is reported as a robustness result under E2.

## Reporting additions (2026-11-04, after the counted run ended, before its results were copied or read)

No prediction's definition changes. Added so that the paper can report what the
pre-registered summary leaves coarse:

- `analyze.py` lists calls that hit a D1 cap (verdict `limit`) with the crashes and
  errors in its robustness section; D1 introduced the verdict.
- The harness records every Valaig run that does not accept as `reject_or_error`.
  `analyze.py` and `make_tables.py` now split these by Valaig's own messages
  (`Tools/ValaigCert.lean` at `6217ed0a`): `s CERTIFICATE UNSAFE` is a rejection; the
  messages printed before any check (`model not wellformed`, `expected single bad ...`,
  `bad not valid in model`, `failed to construct product circuit`) mean the pair is
  outside Valaig's scope; anything else is an error.
- `make_tables.py` writes every study number the manuscript cites as a LaTeX macro, and
  compares Valaig's refusals with its documented scope read from the files (a
  certificate with constraints, a file without exactly one bad literal, or a file
  outside Valaig's well-formedness: a gate reading a variable not below it, or a reset
  reading a variable not below its latch). Tested on the pilot of seed 1 only, where the
  scope read from the files matched Valaig's refusals on all 196 pairs.

## After reading the counted results (2026-11-04)

Changes to reporting only; no verdict and no prediction's definition changed.

- **Capped calls labelled `error`.** The harness looked for the words "out of memory" or
  "time limit" to label a capped Certifaiger call `limit`; Certifaiger's wrapper prints
  neither. It prints `limit generation to 120 seconds and 4096 MB`, and the killed call
  ends with `certifaiger failed with exit code 137`. The 256 release-build calls of the
  current version and the 158 of 10.2.1 recorded as `error` on `order` pairs are these:
  each ended within 2.4 to 4.0 s, far below the 120 s cap, so at the memory cap. Neither
  label is an accept or a reject.
- **Valaig's liveness refusal.** Its parser's message `justice and fairness properties
  not yet supported` (5 fixed pairs, all with liveness sections) is now counted as out of
  scope; the committed list had missed it, and the files-based scope test reads the
  justice and fairness counts.
- **Explanations computed after the fact, labelled as such in the paper:** for the pairs
  Valaig accepts and Certifaiger rejects, whether the witness mutant changes anything
  Valaig reads (diff against the base witness, `valaig_view` in `make_tables.py`); for
  the pairs Valaig rejects and Certifaiger accepts, whether the witness has `= n` mapping
  symbols; the differences D1 and D3 by family.
- **Exploratory, not pre-registered:** the ground truth on all 300 std models rIC3 ran on,
  including the 180 it found unsafe, which have no pairs and so are outside P6
  (`study/p6_all_models.sh`, `results/p6_all_models.csv`): 300 agreements.

## After the final review (2026-11-04)

Post hoc checks, run or computed after the results were read, and marked "post hoc" in
the paper (Section 5 lists them; Section 6 marks each):

- the `order` witnesses converted to binary AIGER by `aigtoaig` and checked again by the
  release build of Certifaiger 10.4.0 under the same caps (`posthoc_order_binary.py`,
  `results/posthoc_order_binary.csv`): all 343 get their ordered original's verdict
  (229 accept, 114 reject). This replaces a pilot observation the draft had cited, which
  the pre-registration says no result may rest on;
- Certifaiger's syntactic stratification test against the reference checker's semantic
  one: on every pair both decided where the test passed, the reference checker found a
  stratification (5,572 of 5,572 for 10.4.0; 3,349 of 3,349 for 10.2.1);
- the reset cycles of the exact witnesses that only the relaxed condition admits
  (`reset_cycle` in `make_tables.py`), the families the differences come from, and the
  explanations of the pairs on which Valaig and Certifaiger differ.

The expectations E1-E3 are now reported in the paper, each with what held and what did
not. The tested build of Certifaiger is named by its own version string, 10.4.0
(`ba86b456`), whose checker source equals 10.3.0's (`results/README.md`, Tool versions);
the pre-registration's "checker source as of 10.3.0" was accurate.

## Certifaiger 10.4.1 (2026-11-07)

Certifaiger 10.4.1 (`b540f0c5`, 2026-11-05) was released after the counted run. Its source
differs from 10.4.0 in how liveness signals are padded, in the name of one liveness check
(Consistent is now Stable) and in comments. Post hoc, its release build (pinned in
`tools/setup_linux.sh` as `CERT_NEW`) ran on all 7,629 pairs under the counted run's caps,
called and classified by the harness's own `run_pairs.certifaiger` (`posthoc_cf1041.py`,
`results/posthoc_cf1041.csv`). It gave every pair the verdict of 10.4.0, with the same
failed checks and stratification messages on 7,628. The exception is Certifaiger's test
`extending_liveness_signal`, invalid in both versions' test lists: 10.4.0 rejects it at
Decrease, 10.4.1 at Liveness. No counted number changes; the paper reports the run as post
hoc.
