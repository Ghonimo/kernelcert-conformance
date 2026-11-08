/-
  AxiomsReport: the axioms of the cited theorems.
  Run: lake env lean AxiomsReport.lean   (CI fails on `sorryAx`; expected: at most
  `propext` and `Quot.sound`).
-/
import KernelCert

-- Core framework
#print axioms KernelCert.safe_iff_no_bad
-- Stratification: relative reset determinacy + reset existence
#print axioms KernelCert.reset_unique
#print axioms KernelCert.reset_unique_of_grounded
#print axioms KernelCert.resetState_isReset
#print axioms KernelCert.reset_exists
-- Metatheorem (Level 1)
#print axioms KernelCert.agreeIn_liftInput
#print axioms KernelCert.witness_sound
-- Level 2: K-restricted checks ⇒ semantic obligations; composite soundness
#print axioms KernelCert.transCheckK_implies_obligation
#print axioms KernelCert.resetCheckK_implies_obligation
#print axioms KernelCert.witness_sound_K
#print axioms KernelCert.witness_sound_K_of_stratification
-- The executable checker: enumeration, single-flip criterion, verdict soundness
#print axioms KernelCert.mem_allFns
#print axioms KernelCert.dep_of_flips
#print axioms KernelCert.respects_of_flips
#print axioms KernelCert.check_sound
-- Certifaiger's own Transition form implies the mechanized one; composed soundness
#print axioms KernelCert.transCheckCF_implies_transCheckK
#print axioms KernelCert.witness_sound_CF
-- End-to-end concrete instances
#print axioms KernelCert.Examples.toy_safe
#print axioms KernelCert.Examples.toy2_safe
#print axioms KernelCert.Examples.toy2_safe_K
#print axioms KernelCert.Examples.toy3_P_not_inductive
#print axioms KernelCert.Examples.toy3_safe
#print axioms KernelCert.Examples.toy3_safe_K
#print axioms KernelCert.Examples.toy4_safe
#print axioms KernelCert.Examples.toyW5_not_stratified
#print axioms KernelCert.Examples.toy5_safe_K
#print axioms KernelCert.Examples.toy6_safe_K
-- Mechanized refutation of the universal-conclusion check forms
#print axioms KernelCert.Counterexamples.universalReset_fails
#print axioms KernelCert.Counterexamples.universalTransition_fails
