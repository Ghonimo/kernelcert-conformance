import KernelCert
open KernelCert
-- Certifaiger's Transition check implies the mechanized one, for every witness.
example {M : SeqCircuit} (κ : Witness M) (h : TransCheckCF κ) : TransCheckK κ :=
  transCheckCF_implies_transCheckK κ h
