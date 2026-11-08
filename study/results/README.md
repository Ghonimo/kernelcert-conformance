# Counted run of PREREGISTRATION.md

Run on deimos.ece.pdx.edu, 2026-11-04 12:57:41 to 13:10:41, by `study/run_counted.sh`
(restart under deviation D1, `DEVIATIONS.md`).

| File | Content |
|---|---|
| `results.csv` | one row per generated pair (7,613): ground truth, reference checker, three Certifaiger builds, Valaig |
| `results_fixed.csv` | the 16 fixed pairs (Certifaiger's tests at `ba86b456`, two hand-made) |
| `ric3_verdicts.csv` | rIC3 on the 300 std models: model, exit code, verdict |
| `run.log` | the driver's log, with the SHA-256 of every tool binary |
| `counted_corpus.tar.gz` | the corpus the run read (models, witnesses, rIC3 certificates, manifest) |
| `counted_logs.tar.gz` | every tool's raw output, `logs/<pair>/` |
| `summary.md`, `summary_fixed.md` | `analyze.py` on the two result files |
| `p6_all_models.csv` | exploratory: ground truth against rIC3 on all 300 std models |
| `posthoc_order_binary.csv` | post hoc: the 343 `order` witnesses converted to binary AIGER by `aigtoaig` and checked again by Certifaiger 10.4.0 (`study/posthoc_order_binary.py`) |
| `posthoc_cf1041.csv` | post hoc: Certifaiger 10.4.1, released after the run, release build, on all 7,629 pairs under the same caps; each outcome next to 10.4.0's (`study/posthoc_cf1041.py`) |
| `posthoc_cf1041_logs.tar.gz` | its raw output per pair (`posthoc_cf1041_logs/<pair>.log`) and its run log, with the SHA-256 of the binaries |

SHA-256 at copy time (equal to the host's):

    62c4507cee89da391bc4124dc4aef213163c7bf72694afa762e5c7f13d80e743  results.csv
    185760d6a8595376db417725dc24e0dc549410b8a6a9e2ec2a40e37172e28753  results_fixed.csv
    22864ddbb1d84cbb1e257624f9c46bb229f28b7894368768e445bec1caf3d186  ric3_verdicts.csv
    99844119691c7868c61fe0099089fd10da53573cfb2f71ce33f2be42f45d101d  counted_corpus.tar.gz
    40eb8d5c4c941ef225621380b2e845bfe8f27b42087afeb6bb3b71397447b8aa  counted_logs.tar.gz

The 10.4.1 run (deimos, 2026-11-07 19:11:20 to 19:16:40), SHA-256 at copy time (equal to
the host's):

    748a340e3506792d19e5b9c3a2f19e2d71b16e11a8833147159b5a9feaf1f835  posthoc_cf1041.csv
    87963524a892fa203ec68442e8732acad8931ec4b95af65884735d956c285ac3  posthoc_cf1041_logs.tar.gz

Reproduce every reported number:

    cd study/results && tar -xzf counted_corpus.tar.gz && tar -xzf counted_logs.tar.gz && cd ../..
    python3 study/analyze.py study/results/results.csv study/results/ric3_verdicts.csv
    python3 study/make_tables.py study/results/results.csv study/results/results_fixed.csv \
        study/results/ric3_verdicts.csv generated study/results/corpus study/corpus/fixed

## Tool versions

Certifaiger at `ba86b456` reports version 10.4.0 (its `CMakeLists.txt`). Its checker
source is that of 10.3.0: `git diff --stat 27d526e3 ba86b456 -- src/` in Certifaiger's
repository is empty; the two commits differ in `scripts/limit.in`, `tests/`,
`CMakeLists.txt` and `util.cmake`. Certifaiger 10.2.1 is `35a0c7f9`.

Certifaiger 10.4.1 is `b540f0c5` (2026-11-05), used post hoc only. Against 10.4.0 its
`src/certifaiger.cpp` changes how liveness signals are padded (`flatten_Q`, `disjoin_Q`),
renames the liveness check Consistent to Stable, and edits comments. SHA-256 of the binaries
the run used: `certifaiger`
`1f3a4e1b44bddbcceeda05bc0390fbc18cff2d86806f8994a82b08d379cec97a`, `check`
`5025dc68cc22a1d8d898757bd59603403e2e89de6d35d2350e618c37850c382a`.
