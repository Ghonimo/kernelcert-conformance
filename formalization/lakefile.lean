import Lake
open Lake DSL

/-- The Lean 4 development behind the paper: the witness-circuit soundness theorem
    for Certifaiger's safety checks (constraints, reset functions that read inputs and
    latches, uninitialized latches, and the reset side condition of Certifaiger 10.3.0),
    and a reference checker compiled from it. Core Lean only. -/
package kernelcert where

@[default_target]
lean_lib KernelCert where

/-- The reference checker: `kcheck <input.json>` (input written by checker/front.py). -/
@[default_target]
lean_exe kcheck where
  root := `Main
