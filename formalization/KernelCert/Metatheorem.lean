/-
  KernelCert.Metatheorem: `witness_sound`, safety of the model from the five obligations.

  Along a constrained run of `M`, a `W`-state that agrees on the shared latches and
  satisfies `C'` follows the run step by step (Reset, then Transition); `P'` holds along
  it (Base, then Step); Property carries `P'` back to `P` at the end. The proof needs no
  side condition, because the obligations supply the witness states directly; the side
  condition enters when Level2.lean derives the obligations from the combinational checks.
-/
import KernelCert.Witness

namespace KernelCert
variable {M : SeqCircuit}

/-- Bounded constructive search for the value of `ιM` at the shared preimage of `i`
    under `inW`: scan the shared-input indices below the bound; `false` if none
    matches. The shared interface is finite and decidably indexed, so the input
    transport needs no choice principle. -/
def liftInputAux (κ : Witness M) (ιM : Input M) (i : Fin κ.W.nI) : Nat → Bool
  | 0 => false
  | j + 1 =>
    if h : j < κ.kIn then
      if κ.inW ⟨j, h⟩ = i then ιM (κ.inM ⟨j, h⟩) else liftInputAux κ ιM i j
    else liftInputAux κ ιM i j

/-- Transport a model input valuation to a witness input valuation along the shared
    inputs (shared inputs copy their value; private witness inputs are set to `false`).
    The input half of the trace-lifting argument. Computable. -/
def liftInput (κ : Witness M) (ιM : Input M) : Input κ.W :=
  fun i => liftInputAux κ ιM i κ.kIn

/-- The scan finds the shared value: at any bound strictly above `j`'s index (and
    within range), the search at `inW j` returns `ιM`'s value at `inM j`
    (injectivity of `inW` identifies the matching index). -/
theorem liftInputAux_spec (κ : Witness M) (ιM : Input M) (j : Fin κ.kIn) :
    ∀ b, j.val < b → b ≤ κ.kIn →
      liftInputAux κ ιM (κ.inW j) b = ιM (κ.inM j) := by
  intro b
  induction b with
  | zero => intro h _; exact absurd h (Nat.not_lt_zero _)
  | succ c ih =>
    intro hj hb
    have hc : c < κ.kIn := hb
    show (if h : c < κ.kIn then
            if κ.inW ⟨c, h⟩ = κ.inW j then ιM (κ.inM ⟨c, h⟩)
            else liftInputAux κ ιM (κ.inW j) c
          else liftInputAux κ ιM (κ.inW j) c) = ιM (κ.inM j)
    rw [dite_eq_left hc]
    by_cases he : κ.inW ⟨c, hc⟩ = κ.inW j
    · rw [ite_eq_left he]
      exact congrArg (fun x => ιM (κ.inM x)) (κ.inW_inj _ _ he)
    · rw [ite_eq_right he]
      have hne : j.val ≠ c := by
        intro hv
        apply he
        have hj' : (⟨c, hc⟩ : Fin κ.kIn) = j := Fin.ext hv.symm
        rw [hj']
      apply ih
      · omega
      · omega

/-- The lifted input agrees with its source on the shared inputs. -/
theorem agreeIn_liftInput (κ : Witness M) (ιM : Input M) :
    AgreeIn κ ιM (liftInput κ ιM) := by
  intro j
  exact (liftInputAux_spec κ ιM j κ.kIn j.isLt (Nat.le_refl _)).symm

/-- **Witness-Circuit Soundness metatheorem (semantic level).** Given a model `M`, a
    witness `κ`, and the five semantic obligations, conclude `Safe M`.

    No property of the model checker that produced `κ`, and no informal argument, appears
    as a hypothesis — only the obligations. Machine-checked; the axiom footprint is
    audited in ../AxiomsReport.lean (no `sorryAx`). -/
theorem witness_sound
    (M : SeqCircuit) (κ : Witness M)
    (h1 : ResetCheck κ) (h2 : TransitionCheck κ) (h3 : PropertyCheck κ)
    (h4 : BaseCheck κ) (h5 : StepCheck κ) :
    Safe M := by
  intro n τ
  -- witness-side inputs: the lift of the model's inputs at every step
  let ι' : Nat → Input κ.W := fun i => liftInput κ (τ.inp i)
  have hAI : ∀ i, AgreeIn κ (τ.inp i) (ι' i) := fun i => agreeIn_liftInput κ (τ.inp i)
  -- along the run there is a shadowing W-state carrying C' and P'
  have key : ∀ i, i ≤ n → ∃ sW : State κ.W,
      Agree κ (τ.st i) sW ∧
      evalC κ.W (ι' i) sW = true ∧
      evalP κ.W (ι' i) sW = true := by
    intro i
    induction i with
    | zero =>
      intro _
      -- initiation: the Reset obligation provides the shadow start state,
      -- the Base obligation starts the invariant
      obtain ⟨sW, hag, hR, hC⟩ :=
        h1 (τ.inp 0) (ι' 0) (τ.st 0) (hAI 0) τ.reset0 (τ.cons_ok 0 (Nat.zero_le n))
      exact ⟨sW, hag, hC, h4 (ι' 0) sW hR hC⟩
    | succ i ih =>
      intro hle
      have hi_le : i ≤ n := Nat.le_of_succ_le hle
      have hi_lt : i < n := Nat.lt_of_succ_le hle
      obtain ⟨sW, hag, hC, hP⟩ := ih hi_le
      -- simulation step: the Transition obligation provides the shadow successor
      obtain ⟨s1', hag1, hF', hC1⟩ :=
        h2 (τ.inp i) (τ.inp (i + 1)) (ι' i) (ι' (i + 1))
          (τ.st i) (τ.st (i + 1)) sW
          (hAI i) (hAI (i + 1)) hag
          (τ.trans_ok i hi_lt) (τ.cons_ok i hi_le) (τ.cons_ok (i + 1) hle) hC
      -- consecution: the Step obligation carries the invariant across it
      exact ⟨s1', hag1, hC1, h5 (ι' i) (ι' (i + 1)) sW s1' hP hF' hC hC1⟩
  obtain ⟨sW, hag, hC, hP⟩ := key n (Nat.le_refl n)
  -- the Property obligation transfers P' at the endpoint back to P
  exact h3 (τ.inp n) (ι' n) (τ.st n) sW (hAI n) hag
    (τ.cons_ok n (Nat.le_refl n)) hC hP

end KernelCert
