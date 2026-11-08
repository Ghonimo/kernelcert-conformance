/-
  AxiomSweep: the union of the axioms used by every constant of the KernelCert namespace.
  Run: lake env lean AxiomSweep.lean
-/
import KernelCert
import Lean
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut used : NameSet := {}
  let mut n : Nat := 0
  for (name, _) in env.constants.toList do
    if (`KernelCert).isPrefixOf name then
      n := n + 1
      for a in (← collectAxioms name) do
        used := used.insert a
  logInfo m!"KernelCert: {n} constants; union of axioms used: {used.toList}"
