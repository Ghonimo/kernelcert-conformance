# KernelCert: a Lean reference for Certifaiger's certificate checks, and a conformance study

| Directory | Contents |
|---|---|
| `formalization/` | Lean 4.34.1 development (core Lean only) and the `kcheck` reference checker; see its README |
| `checker/` | `front.py` (reads AIGER as Certifaiger does), `kc` (front end plus `kcheck`), tests |
| `study/` | pre-registration, deviations, third-party findings, corpus generator, harness, analysis, corpus, results and per-pair logs |

```
(cd formalization && lake build && lake env lean AxiomsReport.lean)   # proofs and axiom audit
(cd formalization && for f in tests/*.lean; do lake env lean "$f" || exit 1; done)   # Lean tests
bash formalization/tests/kcheck_test.sh                            # kcheck on fixtures
python3 -I checker/test_front.py && python3 -I study/tools/test_bfs.py
checker/kc study/corpus/handmade/unmapped_strat_model.aag study/corpus/handmade/unmapped_strat_witness.aag
cd study/results && tar -xzf counted_corpus.tar.gz && tar -xzf counted_logs.tar.gz && cd ../..
python3 -I study/analyze.py study/results/results.csv study/results/ric3_verdicts.csv   # the predictions
python3 -I study/make_tables.py study/results/results.csv study/results/results_fixed.csv \
    study/results/ric3_verdicts.csv generated study/results/corpus study/corpus/fixed       # every number in the paper, in generated/
```

Rerunning the study needs Linux, podman (for rIC3), and the tools built by
`study/tools/setup_linux.sh` and `study/tools/build_lean_tools.sh`; then
`bash study/run_counted.sh ROOT`. The post hoc checks (`study/posthoc_*.py`,
`study/p6_all_models.sh`) run on the same host; their outputs are in `study/results/`,
described in `study/results/README.md`. Certifaiger's test pairs in
`study/corpus/certifaiger_tests/` are Certifaiger's own (MIT license, included).
License: Apache-2.0. Cite via CITATION.cff.
