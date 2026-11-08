import KernelCert.Aig
open KernelCert KernelCert.Aig

/-! The 10.3.0 example as and-inverter graphs (AIGER literal numbering, reencoded:
  inputs first, then latches, then AND gates).
  Model: latch m = var 1 (lit 2), next 2, reset 0 (low), bad 2.
  Witness: latch k = var 1 (lit 2), latch p = var 2 (lit 4), gate var 3 (lit 6) = k ∧ p;
  k: next 2, reset 6; p: next 4, reset 0; bad 2. Shared: witness latch 0 ↔ model latch 0. -/
def gM : Graph := { nI := 0, nL := 1, maxVar := 1, latchNext := #[2], latchReset := #[0],
                    ands := #[], bad := #[2], cons := #[] }
def gW : Graph := { nI := 0, nL := 2, maxVar := 3, latchNext := #[2, 4], latchReset := #[6, 0],
                    ands := #[(6, 2, 4)], bad := #[2], cons := #[] }

-- evaluation: with k = p = 1 the gate is 1; with k = 1, p = 0 it is 0
#guard litVal (evalAll gW (fun i => i.elim0) (fun _ => true)) 6 = true
#guard litVal (evalAll gW (fun i => i.elim0) (fun l => decide (l.val = 0))) 6 = false
#guard litVal (evalAll gW (fun i => i.elim0) (fun l => decide (l.val = 0))) 7 = true

-- the witness interface is built, and the checker accepts
#guard (mkWitness (toCircuit gM) (toCircuit gW) #[(0, 0)] #[]).isSome
#guard match mkWitness (toCircuit gM) (toCircuit gW) #[(0, 0)] #[] with
  | some κ => (runChecks (toCircuit gM) κ).ok
  | none => false

-- control: out-of-range and non-injective mappings are refused
#guard (mkWitness (toCircuit gM) (toCircuit gW) #[(2, 0)] #[]).isNone
#guard (mkWitness (toCircuit gM) (toCircuit gW) #[(0, 0), (1, 0)] #[]).isNone

/-! Control: an unsafe model (the latch toggles, so it is high at time 1). No witness
  may pass; the self-witness fails Base or Step. -/
def gU : Graph := { nI := 0, nL := 1, maxVar := 1, latchNext := #[3], latchReset := #[0],
                    ands := #[], bad := #[2], cons := #[] }
#guard match mkWitness (toCircuit gU) (toCircuit gU) #[(0, 0)] #[] with
  | some κ => !(runChecks (toCircuit gU) κ).ok
  | none => false
