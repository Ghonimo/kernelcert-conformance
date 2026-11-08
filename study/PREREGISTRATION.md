> This copy differs from the file committed before the counted run (repository commit
> 6bf5978, 2026-11-04 12:46:53 -0800; SHA-256 of that file
> 8eb1f534e2812720babefb69aa1616a29dcd222293b13d96f99bcf95559af234) in one rule under
> Rules, on acceptances of unsafe models. Where this copy reads "one independent
> confirmation", the original names an internal review step and gives the path of an
> internal checklist file; the original also names the person who approves the message
> to the maintainers. Nothing else differs.

# Conformance study: pre-registration

Written 2026-11-04, before any counted run. The commit that adds this file fixes the
generator, the harness and the analysis; their first-commit dates and this file's are the
order of record. Pilot runs (seeds 1, 2, 3; scratch directories, not archived as results)
were used only to debug the tools and to size the corpus; their outputs inform nothing
below except the generator tuning noted in "Pilot use".

## Questions

- **RQ1 (soundness in practice).** Does any checker accept a witness for an unsafe model?
- **RQ2 (conformance).** On the pairs the reference checker covers, how do Certifaiger's
  verdicts relate to the mechanized checks?
- **RQ3 (the September 2026 change).** Which witnesses does Certifaiger 10.3.0 accept that
  10.2.1 rejects, and does the mechanized theorem cover them?
- **RQ4 (scope and cost).** What share of witnesses falls outside the mechanized model, for
  which reasons, and what does the reference check cost?

## Tools (pinned)

| Role | Tool | Version |
|---|---|---|
| reference checker | `checker/front.py` + `kcheck` (formalization/, Lean 4.34.1) | this commit |
| ground truth | `study/tools/bfs.py` (own reader, shares no code with the checker) | this commit |
| tool under test | Certifaiger, release build | `ba86b456` (checker source as of 10.3.0) |
| tool under test | Certifaiger, assertions enabled (`-DASSERT=ON`) | `ba86b456` |
| tool under test | Certifaiger 10.2.1, release build | `35a0c7f9`, with the current build's AIGER tools and Kissat |
| verified checker | Valaig `valaigcert` (calls an external CaDiCaL) | `6217ed0a`; CaDiCaL `rel-3.0.1` |
| model checker | rIC3 (`-e ic3`), container image | v1.5.2, digest `sha256:60e8fcb3…` |

Host: deimos.ece.pdx.edu (Rocky 9, 32 cores). Build: `study/tools/setup_linux.sh`,
`study/tools/build_lean_tools.sh`.

## Corpus

1. `make_corpus.py stage1 OUT --seed 20261104 --models 600` (300 std, 300 ext models).
2. `ric3_certificates.sh OUT TOOLS 16`: rIC3 on every std model, 120 s each; certificates
   of the models it proves safe.
3. `make_corpus.py stage3 OUT --seed 20261104`: rIC3 certificates and their mutants.
4. The fixed pairs in `study/corpus/fixed/manifest.csv`: Certifaiger's 14 test pairs at
   `ba86b456` and the 2 hand-made pairs.

Families, as defined in `make_corpus.py`: exact, aux, kp, d1, d3, ric3, mut, mmut, order.
The corpus files are archived with the results, so the run can be repeated without
regenerating them.

## Measurements

`run_pairs.py` per pair: the ground truth on the model; the reference checker's verdict and
per-check entries, or its refusal reason; `kcheck --diag` when the reference checker
accepts and Certifaiger current rejects; the three Certifaiger builds (verdict, the checks
it names as failed, "not stratified", exit code); Valaig. Timeout 300 s per tool call
(1800 s for `--diag`). Every verdict is rebuilt by `analyze.py` from `results.csv`, and the
raw log of every tool call is kept under `logs/<pair>/`.

## Predictions (operational definitions in `analyze.py`)

- **P1** No checker (Certifaiger current, current with assertions, 10.2.1, Valaig) accepts
  a pair whose model the ground truth finds unsafe.
- **P2** The reference checker accepts no such pair. (Implied by `check_sound`; a violation
  would locate a fault in the front end, the evaluation, or the ground truth.)
- **P3** On the pairs the reference checker does not refuse, Certifaiger current never
  accepts a pair the reference checker rejects. (Its five checks imply the mechanized
  ones: four are the same formulas, and `transCheckCF_implies_transCheckK` covers
  Transition; its syntactic side condition implies the semantic one.)
- **P4** Every pair the reference checker accepts and Certifaiger current rejects is
  explained by D1, D2 or D3 as `analyze.py` classifies them.
- **P5** Every pair Certifaiger current accepts and 10.2.1 rejects is one where 10.2.1
  reports "not stratified", and the reference checker accepts it.
- **P6** The ground truth agrees with rIC3 on every std model both decide.

Expectations, reported but not counted as predictions:
- **E1** The d1 pairs are rejected by Certifaiger on Transition (D1); the d3 pairs are
  rejected by both builds as "not stratified" (D3); the kp pairs are rejected by 10.2.1 as
  "not stratified" and accepted by the current build.
- **E2** The order pairs (valid ASCII AIGER; the AIGER format leaves gate order free) make
  the assertion build fail in `unroll` and the release builds end without a verdict; no
  Certifaiger build accepts one. The reference checker refuses them.
- **E3** Valaig decides only std pairs without constraints, with one bad literal.

## Rules

- One counted run. A tool call that fails for a host reason (out of memory, quota, killed)
  is rerun once and logged in `study/DEVIATIONS.md`; nothing is rerun to change a verdict.
- A falsified prediction is reported as falsified, with the pairs, in the paper.
- Any acceptance of an unsafe model by a third-party tool gets one independent
  confirmation and a message to its maintainers before publication; the paper reports
  their answer.

## Pilot use

The pilots led to two generator changes before this file: the bad signal is a conjunction
of two literals in 60% of models (too few models were safe), and the d1 and d3 families
were added because no pilot pair exercised divergences D1 and D3. No pilot verdict is
reported as a result.
