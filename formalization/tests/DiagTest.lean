import KernelCert
open KernelCert

/-! D1: Certifaiger's Transition check leaves the witness's private latches free at the
  second time point; the mechanized check uses their successor values.
  Model: latch m toggles (reset low), no bad signal.
  Witness: latch k (shared with m) toggles too; private latch p resets low and stays low;
  constraint C' = ¬k ∨ ¬p; no bad signal. Sound, accepted by the mechanized checks,
  and failing Certifaiger's form of the Transition check (k high, p free high). -/
def toyM7 : SeqCircuit where
  nI := 0
  nL := 1
  resetVal := fun _ _ _ => false
  next := fun _ s _ => !(s 0)
  good := fun _ _ => true
  cons := fun _ _ => true

def toyW7W : SeqCircuit where
  nI := 0
  nL := 2
  resetVal := fun _ _ _ => false
  next := fun _ s l => if l.val = 0 then !(s 0) else false
  good := fun _ _ => true
  cons := fun _ s => !(s 0) || !(s 1)

def toyW7 : Witness toyM7 where
  W := toyW7W
  k := 1
  embM := fun j => j
  embW := fun _ => (0 : Fin 2)
  embM_inj := fun _ _ h => h
  embW_inj := fun a b _ => by have := a.isLt; have := b.isLt; exact Fin.ext (by omega)
  kIn := 0
  inM := fun j => j.elim0
  inW := fun j => j.elim0
  inM_inj := fun a => a.elim0
  inW_inj := fun a => a.elim0

#guard (runChecks toyM7 toyW7).ok
#guard !(decide (TransCheckCF toyW7))
#guard !(decide (TransCheckD1 toyW7))
-- on a witness without private latches the three transition forms agree
#guard decide (TransCheckCF KernelCert.Examples.toyW) && decide (TransCheckD1 KernelCert.Examples.toyW)
