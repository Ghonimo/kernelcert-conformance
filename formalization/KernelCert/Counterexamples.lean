/-
  KernelCert.Counterexamples: the universal forms of the Reset and Transition checks fail
  for a witness whose reset and next functions pin its private latch.

  Stated universally ("every witness state that agrees on the shared latches is a reset",
  resp. "is a successor"), the checks fail for the witness `toyW2` of Examples.lean, whose
  private latch the agreement leaves free while `R'` and `F'` pin it. `toy2_safe` shows
  that the existential forms of Witness.lean admit the same witness. These theorems guard
  the existential shape of the obligations.
-/
import KernelCert.Examples

namespace KernelCert
namespace Counterexamples
open Examples

variable {M : SeqCircuit}

/-- The REFUTED universal-conclusion reset form: every witness state that K-agrees
    with a constrained model reset is itself a full witness reset. -/
def UniversalResetCheck (κ : Witness M) : Prop :=
  ∀ (ιM : Input M) (ιW : Input κ.W) (sM : State M) (sW : State κ.W),
    AgreeIn κ ιM ιW → R M ιM sM → evalC M ιM sM = true →
    Agree κ sM sW → R κ.W ιW sW

/-- The REFUTED universal-conclusion transition form: every witness state that
    K-agrees with the model's post-state is an `F'`-successor of the given witness
    pre-state. -/
def UniversalTransitionCheck (κ : Witness M) : Prop :=
  ∀ (ι0 ι1 : Input M) (ιW0 ιW1 : Input κ.W)
    (s0 s1 : State M) (s0' s1' : State κ.W),
    AgreeIn κ ι0 ιW0 → AgreeIn κ ι1 ιW1 → Agree κ s0 s0' →
    F M ι0 s0 s1 → evalC M ι0 s0 = true → evalC M ι1 s1 = true →
    evalC κ.W ιW0 s0' = true → Agree κ s1 s1' →
    F κ.W ιW0 s0' s1'

/-- The universal reset form is FALSE for the aux-latch witness `toyW2`: the all-false
    model reset K-agrees with the witness state whose private latch is high, but that
    state violates the private latch's reset equation. -/
theorem universalReset_fails : ¬ UniversalResetCheck toyW2 := by
  intro h
  have hbad := h (fun i => i.elim0) (fun i => i.elim0)
      (fun _ => false)
      (fun l => if l.val = 0 then false else true)
      (fun j => j.elim0)
      (fun _ => rfl)
      rfl
      (fun _ => rfl)
  have hcontra : (true : Bool) = false := hbad (1 : Fin 2)
  exact Bool.noConfusion hcontra

/-- The universal transition form is FALSE for `toyW2`: the constantly-false model
    step K-agrees with a successor whose private latch is high, but `F'` (functional,
    constantly false) pins that latch low. -/
theorem universalTransition_fails : ¬ UniversalTransitionCheck toyW2 := by
  intro h
  have hbad := h (fun i => i.elim0) (fun i => i.elim0)
      (fun i => i.elim0) (fun i => i.elim0)
      (fun _ => false) (fun _ => false)
      (fun _ => false)
      (fun l => if l.val = 0 then false else true)
      (fun j => j.elim0) (fun j => j.elim0)
      (fun _ => rfl)
      (fun _ => rfl)
      rfl rfl rfl
      (fun _ => rfl)
  have hcontra : (true : Bool) = false := hbad (1 : Fin 2)
  exact Bool.noConfusion hcontra

end Counterexamples
end KernelCert
