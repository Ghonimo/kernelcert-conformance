/-
  KernelCert.Diag — Certifaiger's own form of the Transition check, for attributing
  disagreements. Not used by the verdict, and no theorem rests on it.

  Certifaiger (src/certifaiger.cpp, `simulates`) checks
      F_st[K] ∧ C_s ∧ C_t ∧ C'_s → F'_st[K] ∧ C'_t
  over three copies of both circuits with latches turned into free variables. Two
  things are free there that the mechanized `TransCheckK` fixes:
  * D1: the witness's private latches at the second time point (C'_t is required for
    every value of them, not only for their successor values);
  * D2: the model's latches outside K at the second time point (C_t is assumed for every
    value of them, not only for the model's successor).
  Both make Certifaiger's check stronger than the mechanized one: what Certifaiger
  accepts, `TransCheckK` accepts.
-/
import KernelCert.Decide

namespace KernelCert
variable {M : SeqCircuit}

/-- Certifaiger's Transition check, as its source encodes it. -/
def TransCheckCF (κ : Witness M) : Prop :=
  ∀ (ι0 : Input M) (s0 : State M), evalC M ι0 s0 = true →
  ∀ (ι1 : Input M) (s1 : State M),
    (∀ j : Fin κ.k, s1 (κ.embM j) = M.next ι0 s0 (κ.embM j)) → evalC M ι1 s1 = true →
  ∀ s0' : State κ.W, Agree κ s0 s0' →
  ∀ ιW0 : Input κ.W, AgreeIn κ ι0 ιW0 → evalC κ.W ιW0 s0' = true →
  ∀ s1' : State κ.W, Agree κ s1 s1' →
  ∀ ιW1 : Input κ.W, AgreeIn κ ι1 ιW1 →
    (∀ j : Fin κ.k, s1' (κ.embW j) = κ.W.next ιW0 s0' (κ.embW j)) ∧
    evalC κ.W ιW1 s1' = true

instance (κ : Witness M) : Decidable (TransCheckCF κ) := by
  unfold TransCheckCF; infer_instance

/-- The mechanized Transition check with only D1 changed: the model's successor is the
    real one, the witness's private latches at the second time point are free. -/
def TransCheckD1 (κ : Witness M) : Prop :=
  ∀ (ι0 : Input M) (s0 : State M), evalC M ι0 s0 = true →
  ∀ ι1 : Input M, evalC M ι1 (fun l => M.next ι0 s0 l) = true →
  ∀ s0' : State κ.W, Agree κ s0 s0' →
  ∀ ιW0 : Input κ.W, AgreeIn κ ι0 ιW0 → evalC κ.W ιW0 s0' = true →
  ∀ s1' : State κ.W, Agree κ (fun l => M.next ι0 s0 l) s1' →
  ∀ ιW1 : Input κ.W, AgreeIn κ ι1 ιW1 →
    (∀ j : Fin κ.k, s1' (κ.embW j) = κ.W.next ιW0 s0' (κ.embW j)) ∧
    evalC κ.W ιW1 s1' = true

instance (κ : Witness M) : Decidable (TransCheckD1 κ) := by
  unfold TransCheckD1; infer_instance

end KernelCert

namespace KernelCert
variable {M : SeqCircuit}

/-- The witness state that agrees with `sM` on the shared latches and with `sW`
    elsewhere. -/
def mixShared (κ : Witness M) (sM : State M) (sW : State κ.W) : State κ.W :=
  fun l => (sharedVal? κ sM l κ.k).getD (sW l)

theorem mixShared_shared (κ : Witness M) (sM : State M) (sW : State κ.W) (j : Fin κ.k) :
    mixShared κ sM sW (κ.embW j) = sM (κ.embM j) := by
  simp only [mixShared]
  rw [sharedVal?_shared κ sM j κ.k j.isLt (Nat.le_refl _)]
  rfl

theorem mixShared_private (κ : Witness M) (sM : State M) (sW : State κ.W) (l : Fin κ.W.nL)
    (hns : ¬ ∃ j : Fin κ.k, κ.embW j = l) : mixShared κ sM sW l = sW l := by
  simp only [mixShared]
  rw [sharedVal?_private κ sM l hns]
  rfl

/-- **Certifaiger's Transition check implies the mechanized one.** Instantiate
    Certifaiger's check at the witness state that copies the model's successor on the
    shared latches and the witness's own successor elsewhere; its conclusion pins the
    shared latches, and then that state is the witness's successor. -/
theorem transCheckCF_implies_transCheckK (κ : Witness M) (h : TransCheckCF κ) :
    TransCheckK κ := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' hAI0 hAI1 hag hF hC0 hC1 hC0'
  let succ : State κ.W := fun l => κ.W.next ιW0 s0' l
  have hag1 : Agree κ s1 (mixShared κ s1 succ) :=
    fun j => (mixShared_shared κ s1 succ j).symm
  obtain ⟨hK, hC'⟩ := h ι0 s0 hC0 ι1 s1 (fun j => hF (κ.embM j)) hC1 s0' hag ιW0 hAI0 hC0'
    (mixShared κ s1 succ) hag1 ιW1 hAI1
  have hK' : ∀ j, s1 (κ.embM j) = κ.W.next ιW0 s0' (κ.embW j) :=
    fun j => (hag1 j).trans (hK j)
  have heq : mixShared κ s1 succ = succ := by
    funext l
    by_cases hs : ∃ j : Fin κ.k, κ.embW j = l
    · obtain ⟨j, rfl⟩ := hs
      rw [mixShared_shared]
      exact hK' j
    · exact mixShared_private κ s1 succ l hs
  refine ⟨hK', ?_⟩
  rw [heq] at hC'
  exact hC'

/-- **Soundness of Certifaiger's checks as its source states them.** Its Reset, Safety,
    Base and Inductive checks are the formulas of `ResetCheckK`, `PropertyCheck`,
    `BaseCheck` and `StepCheck`; its Transition check is `TransCheckCF`. With the
    10.3.0 side condition in its semantic form, they imply safety. -/
theorem witness_sound_CF
    (M : SeqCircuit) (κ : Witness M) (strat : UnmappedStratification κ)
    (h1 : ResetCheckK κ) (h2 : TransCheckCF κ) (h3 : PropertyCheck κ)
    (h4 : BaseCheck κ) (h5 : StepCheck κ) :
    Safe M :=
  witness_sound_K M κ strat h1 (transCheckCF_implies_transCheckK κ h2) h3 h4 h5

end KernelCert
