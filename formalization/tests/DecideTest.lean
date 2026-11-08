import KernelCert
open KernelCert KernelCert.Examples

/-! Accept: every worked instance passes all checks and the side condition. -/
#guard (runChecks toyM toyW).ok
#guard (runChecks toyM toyW2).ok
#guard (runChecks toyM3 toyW3).ok
#guard (runChecks toyM4 toyW4).ok
#guard (runChecks toyM5 toyW5).ok
#guard (runChecks toyM6 toyW6).ok

/-! Controls that must fail. -/

/-- `toyM3` certified by itself: `P = ¬x` is not 1-inductive, so Step must fail and
    nothing else. -/
def toyW3self : Witness toyM3 where
  W := toyM3
  k := 2
  embM := fun j => j
  embW := fun j => j
  embM_inj := fun _ _ h => h
  embW_inj := fun _ _ h => h
  kIn := 1
  inM := fun j => j
  inW := fun j => j
  inM_inj := fun _ _ h => h
  inW_inj := fun _ _ h => h
#guard !(runChecks toyM3 toyW3self).ok
#guard !(runChecks toyM3 toyW3self).step
#guard (runChecks toyM3 toyW3self).reset && (runChecks toyM3 toyW3self).trans
#guard (runChecks toyM3 toyW3self).prop && (runChecks toyM3 toyW3self).base

/-- A witness for `toyM4` that resets its copy of the uninitialized latch to `false`:
    the model's reset allows the latch high, so Reset must fail. -/
def toyW4strictW : SeqCircuit where
  nI := 0
  nL := 2
  resetVal := fun _ _ _ => false
  next := fun _ s _ => s 0
  good := fun _ s => !(s 0)
  cons := fun _ _ => true
def toyW4strict : Witness toyM4 where
  W := toyW4strictW
  k := 2
  embM := fun j => j
  embW := fun j => j
  embM_inj := fun _ _ h => h
  embW_inj := fun _ _ h => h
  kIn := 0
  inM := fun j => j.elim0
  inW := fun j => j.elim0
  inM_inj := fun a => a.elim0
  inW_inj := fun a => a.elim0
#guard !(runChecks toyM4 toyW4strict).reset

/-- A private latch whose reset is its own negation: no stratification exists. -/
def toyW5cycW : SeqCircuit where
  nI := 0
  nL := 2
  resetVal := fun _ s l => if l.val = 0 then false else !(s 1)
  next := fun _ s l => s l
  good := fun _ s => !(s 0)
  cons := fun _ _ => true
def toyW5cyc : Witness toyM5 where
  W := toyW5cycW
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
#guard !(runChecks toyM5 toyW5cyc).strat

/-! The soundness theorem applies to a checker verdict. -/
example (h : (runChecks toyM5 toyW5).ok = true) : Safe toyM5 := check_sound toyM5 toyW5 h
