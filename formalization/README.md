# `formalization/`: the Lean 4 development and the `kcheck` reference checker

Core Lean 4.34.1, no library dependency.

```
lake build                         # library and the kcheck executable
lake env lean AxiomsReport.lean    # axiom audit: expect propext and Quot.sound at most, no sorryAx
for t in tests/*.lean; do lake env lean "$t" || echo "FAIL $t"; done
bash tests/kcheck_test.sh          # exit codes of kcheck on fixtures: 0 accept, 1 reject, 2 refused
```

## What is proved

| File | Main results |
|---|---|
| `KernelCert/Circuit.lean` | `SeqCircuit` (reset values may read inputs and latches), constrained runs, `Safe` |
| `KernelCert/Witness.lean` | `Witness` (shared latches and inputs as injective maps), the five obligations |
| `KernelCert/Metatheorem.lean` | `witness_sound`: the five obligations imply `Safe M` |
| `KernelCert/Stratification.lean` | FMCAD'22 stratification; `reset_exists`, `reset_unique` (relative determinacy) |
| `KernelCert/Level2.lean` | the combinational checks `ResetCheckK`, `TransCheckK`; `UnmappedStratification` (Certifaiger 10.3.0's side condition); `resetCheckK_implies_obligation`; `witness_sound_K`; `witness_sound_K_of_stratification` |
| `KernelCert/Diag.lean` | `TransCheckCF` (Certifaiger's own Transition formula); `transCheckCF_implies_transCheckK`; `witness_sound_CF` |
| `KernelCert/Enum.lean` | `allFns`, `mem_allFns`; decidability of quantifiers over valuations; `dep_of_flips` |
| `KernelCert/Decide.lean` | reordered checks and their soundness; `findStrat`; `runChecks`; `check_sound` |
| `KernelCert/Aig.lean` | and-inverter graphs as circuits (`toCircuit`); `mkWitness` with run-time range and injectivity checks |
| `KernelCert/Examples.lean` | worked instances, including `toyW5_not_stratified` and `toy5_safe_K` (a witness only the 10.3.0 condition admits) and `toy6_safe_K` (input-dependent resets) |
| `KernelCert/Counterexamples.lean` | the universal forms of Reset and Transition fail for a witness whose private latch its reset and next functions pin (`toyW2`) |
| `Main.lean` | the `kcheck` executable |

## `kcheck`

`kcheck input.json [--diag]` reads the JSON that `../checker/front.py` writes from two
AIGER files and prints one verdict line. Use `../checker/kc MODEL WITNESS` for both steps.
`check_sound` proves that an accepting report implies `Safe M` for the circuits `kcheck`
builds; running it also trusts the Lean compiler, and the front end for the meaning of the
files. With `--diag` it also decides Certifaiger's form of the Transition check and the
D1 variant (diagnostics only).
