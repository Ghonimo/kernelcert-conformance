/-
  KernelCert.Aig — and-inverter graphs as `SeqCircuit`s, and the witness interface built
  from a list of shared index pairs.

  A `Graph` uses AIGER's literal numbering in the reencoded layout that Certifaiger
  requires: variable 0 is the constant, inputs are variables `1 … nI`, latches
  `nI + 1 … nI + nL`, and AND gates follow. `evalAll` computes every variable from an
  input and a latch valuation in one pass over the gates, so the gates must be listed
  so that each reads only earlier variables (the front end orders them). A latch's
  reset is any literal, so resets may read inputs, latches and gates.

  What is trusted here: that `toCircuit` is the meaning of the AIGER file the front end
  read. The checker's soundness (`check_sound`) holds for whatever `SeqCircuit` and
  `Witness` this module builds.
-/
import KernelCert.Decide

namespace KernelCert
namespace Aig

/-- An and-inverter graph with latches, in AIGER literal numbering. -/
structure Graph where
  nI : Nat
  nL : Nat
  maxVar : Nat
  /-- next-state literal of each latch -/
  latchNext : Array Nat
  /-- reset literal of each latch; the latch's own literal means uninitialized -/
  latchReset : Array Nat
  /-- `(lhs, rhs0, rhs1)` -/
  ands : Array (Nat × Nat × Nat)
  /-- bad-state literals; the property holds when all are low -/
  bad : Array Nat
  /-- invariant constraint literals; all must be high -/
  cons : Array Nat
deriving Repr

/-- Value of a literal under variable values: the variable's value, negated for odd
    literals. -/
@[inline] def litVal (vals : Array Bool) (lit : Nat) : Bool :=
  vals.getD (lit / 2) false != (lit % 2 == 1)

/-- All variable values for an input and a latch valuation, in one pass. -/
def evalAll (g : Graph) (ι : Fin g.nI → Bool) (s : Fin g.nL → Bool) : Array Bool :=
  let v0 := Array.replicate (g.maxVar + 1) false
  let v1 := (List.finRange g.nI).foldl (fun v i => v.modify (i.val + 1) fun _ => ι i) v0
  let v2 := (List.finRange g.nL).foldl
    (fun v l => v.modify (g.nI + l.val + 1) fun _ => s l) v1
  g.ands.foldl (fun v a => v.modify (a.1 / 2) fun _ => litVal v a.2.1 && litVal v a.2.2) v2

/-- The circuit an and-inverter graph denotes. -/
def toCircuit (g : Graph) : SeqCircuit where
  nI := g.nI
  nL := g.nL
  resetVal := fun ι s l => litVal (evalAll g ι s) (g.latchReset.getD l.val 0)
  next := fun ι s l => litVal (evalAll g ι s) (g.latchNext.getD l.val 0)
  good := fun ι s => g.bad.all fun b => !(litVal (evalAll g ι s) b)
  cons := fun ι s => g.cons.all fun c => litVal (evalAll g ι s) c

/-- The witness interface from shared index pairs `(witness index, model index)` for
    latches (`lp`) and inputs (`ip`). Refused (`none`) if an index is out of range or a
    side is not injective. -/
def mkWitness (M W : SeqCircuit) (lp ip : Array (Nat × Nat)) : Option (Witness M) :=
  if hL : ∀ j : Fin lp.size, lp[j].1 < W.nL ∧ lp[j].2 < M.nL then
    if hI : ∀ j : Fin ip.size, ip[j].1 < W.nI ∧ ip[j].2 < M.nI then
      let embM : Fin lp.size → Fin M.nL := fun j => ⟨lp[j].2, (hL j).2⟩
      let embW : Fin lp.size → Fin W.nL := fun j => ⟨lp[j].1, (hL j).1⟩
      let inM : Fin ip.size → Fin M.nI := fun j => ⟨ip[j].2, (hI j).2⟩
      let inW : Fin ip.size → Fin W.nI := fun j => ⟨ip[j].1, (hI j).1⟩
      if h1 : ∀ a b : Fin lp.size, embM a = embM b → a = b then
        if h2 : ∀ a b : Fin lp.size, embW a = embW b → a = b then
          if h3 : ∀ a b : Fin ip.size, inM a = inM b → a = b then
            if h4 : ∀ a b : Fin ip.size, inW a = inW b → a = b then
              some { W := W, k := lp.size, embM := embM, embW := embW,
                     embM_inj := h1, embW_inj := h2,
                     kIn := ip.size, inM := inM, inW := inW,
                     inM_inj := h3, inW_inj := h4 }
            else none
          else none
        else none
      else none
    else none
  else none

end Aig
end KernelCert
