/-
  KernelCert.Decide — deciding the checks by evaluation, and the soundness of the
  verdict.

  Each check is restated with its quantifiers in an order that lets evaluation stop
  early (hypotheses that filter come first; the successor state is computed rather
  than enumerated), and each restatement is proved to imply the check it replaces.
  The restatements are decidable through the enumeration instances of Enum.lean, so
  `decide` evaluates them. The side condition is found by an untrusted search for
  levels, which `RespectsFlip` then checks; `respects_of_flips` turns a passing check
  into the dependency condition `UnmappedStratification` needs.

  `check_sound`: if every entry of `runChecks M κ` is `true`, then `Safe M`. The
  theorem is about the functions as written; a verdict computed by compiled code also
  trusts the compiler.
-/
import KernelCert.Level2
import KernelCert.Enum

namespace KernelCert
variable {M : SeqCircuit}

/-! ### Decidability of the basic relations -/

instance (κ : Witness M) (sM : State M) (sW : State κ.W) : Decidable (Agree κ sM sW) := by
  unfold Agree; infer_instance

instance (κ : Witness M) (ιM : Input M) (ιW : Input κ.W) :
    Decidable (AgreeIn κ ιM ιW) := by
  unfold AgreeIn; infer_instance

instance (κ : Witness M) (l : Fin κ.W.nL) : Decidable (IsShared κ l) := by
  unfold IsShared; infer_instance

instance (W : SeqCircuit) (l : Fin W.nL) : Decidable (SelfReset W l) := by
  unfold SelfReset; infer_instance

/-! ### The checks, reordered for evaluation -/

/-- `ResetCheckK` with the filtering hypotheses first. -/
def ResetCheckKo (κ : Witness M) : Prop :=
  ∀ (ιM : Input M) (sM : State M),
    (∀ j : Fin κ.k, sM (κ.embM j) = M.resetVal ιM sM (κ.embM j)) →
    evalC M ιM sM = true →
    ∀ sW : State κ.W, Agree κ sM sW →
    ∀ ιW : Input κ.W, AgreeIn κ ιM ιW →
      (∀ j : Fin κ.k, sW (κ.embW j) = κ.W.resetVal ιW sW (κ.embW j)) ∧
      evalC κ.W ιW sW = true

theorem ResetCheckKo.sound {κ : Witness M} (h : ResetCheckKo κ) : ResetCheckK κ :=
  fun ιM ιW sM sW hAI hag hRK hC => h ιM sM hRK hC sW hag ιW hAI

instance (κ : Witness M) : Decidable (ResetCheckKo κ) := by
  unfold ResetCheckKo; infer_instance

/-- `TransCheckK` with the model's successor computed rather than enumerated. -/
def TransCheckKo (κ : Witness M) : Prop :=
  ∀ (ι0 : Input M) (s0 : State M), evalC M ι0 s0 = true →
    ∀ ι1 : Input M, evalC M ι1 (fun l => M.next ι0 s0 l) = true →
    ∀ s0' : State κ.W, Agree κ s0 s0' →
    ∀ ιW0 : Input κ.W, AgreeIn κ ι0 ιW0 → evalC κ.W ιW0 s0' = true →
      (∀ j : Fin κ.k, M.next ι0 s0 (κ.embM j) = κ.W.next ιW0 s0' (κ.embW j)) ∧
      ∀ ιW1 : Input κ.W, AgreeIn κ ι1 ιW1 →
        evalC κ.W ιW1 (fun l => κ.W.next ιW0 s0' l) = true

theorem TransCheckKo.sound {κ : Witness M} (h : TransCheckKo κ) : TransCheckK κ := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' hAI0 hAI1 hag hF hC0 hC1 hC0'
  have hs1 : s1 = fun l => M.next ι0 s0 l := funext hF
  subst hs1
  obtain ⟨hK, hC'⟩ := h ι0 s0 hC0 ι1 hC1 s0' hag ιW0 hAI0 hC0'
  exact ⟨hK, hC' ιW1 hAI1⟩

instance (κ : Witness M) : Decidable (TransCheckKo κ) := by
  unfold TransCheckKo; infer_instance

/-- `PropertyCheck` with the filtering hypotheses first. -/
def PropertyCheckO (κ : Witness M) : Prop :=
  ∀ (ιM : Input M) (sM : State M), evalC M ιM sM = true →
    ∀ sW : State κ.W, Agree κ sM sW →
    ∀ ιW : Input κ.W, AgreeIn κ ιM ιW → evalC κ.W ιW sW = true →
      evalP κ.W ιW sW = true → evalP M ιM sM = true

theorem PropertyCheckO.sound {κ : Witness M} (h : PropertyCheckO κ) : PropertyCheck κ :=
  fun ιM ιW sM sW hAI hag hC hC' hP' => h ιM sM hC sW hag ιW hAI hC' hP'

instance (κ : Witness M) : Decidable (PropertyCheckO κ) := by
  unfold PropertyCheckO; infer_instance

instance (κ : Witness M) : Decidable (BaseCheck κ) := by
  unfold BaseCheck R; infer_instance

/-- `StepCheck` with the witness's successor computed rather than enumerated. -/
def StepCheckO (κ : Witness M) : Prop :=
  ∀ (ι0 : Input κ.W) (s0' : State κ.W),
    evalP κ.W ι0 s0' = true → evalC κ.W ι0 s0' = true →
    ∀ ι1 : Input κ.W, evalC κ.W ι1 (fun l => κ.W.next ι0 s0' l) = true →
      evalP κ.W ι1 (fun l => κ.W.next ι0 s0' l) = true

theorem StepCheckO.sound {κ : Witness M} (h : StepCheckO κ) : StepCheck κ := by
  intro ι0 ι1 s0' s1' hP hF hC0 hC1
  have hs : s1' = fun l => κ.W.next ι0 s0' l := funext hF
  subst hs
  exact h ι0 s0' hP hC0 ι1 hC1

instance (κ : Witness M) : Decidable (StepCheckO κ) := by
  unfold StepCheckO; infer_instance

/-! ### The side condition -/

/-- The dependency condition of `UnmappedStratification`, stated over single flips:
    negating any latch that is neither of lower level nor shared leaves the reset
    value of every private, non-free latch unchanged. -/
def RespectsFlip (κ : Witness M) (lvl : Fin κ.W.nL → Nat) (free : Fin κ.W.nL → Bool) :
    Prop :=
  ∀ l : Fin κ.W.nL, ¬ IsShared κ l → free l = false →
    ∀ (ι : Input κ.W) (s : State κ.W) (b : Fin κ.W.nL),
      ¬ (lvl b < lvl l ∨ IsShared κ b) →
      κ.W.resetVal ι (flipAt s b) l = κ.W.resetVal ι s l

instance (κ : Witness M) (lvl : Fin κ.W.nL → Nat) (free : Fin κ.W.nL → Bool) :
    Decidable (RespectsFlip κ lvl free) := by
  unfold RespectsFlip; infer_instance

theorem respects_of_flips {κ : Witness M} {lvl : Fin κ.W.nL → Nat}
    {free : Fin κ.W.nL → Bool} (h : RespectsFlip κ lvl free) :
    ∀ l, ¬ IsShared κ l → free l = false →
      ∀ (ι : Input κ.W) (s s' : State κ.W),
        (∀ b, lvl b < lvl l ∨ IsShared κ b → s b = s' b) →
        κ.W.resetVal ι s l = κ.W.resetVal ι s' l := by
  intro l hns hf ι s s' hag
  exact dep_of_flips (fun s => κ.W.resetVal ι s l)
    (fun b => lvl b < lvl l ∨ IsShared κ b) (fun s b hb => h l hns hf ι s b hb) s s' hag

/-- Does latch `l`'s reset value change when latch `b` is negated, for some input and
    state? (Used only to propose levels; nothing relies on it being right.) -/
def depB (W : SeqCircuit) (l b : Fin W.nL) : Bool :=
  (allFns W.nI).any fun ι => (allFns W.nL).any fun s =>
    W.resetVal ι (flipAt s b) l != W.resetVal ι s l

/-- Proposed levels: 0 for shared and free latches; for the others, one more than the
    highest private latch their reset reads, by `n + 1` rounds of relaxation. Untrusted:
    `RespectsFlip` checks the result. -/
def candidateLevels (κ : Witness M) (free : Fin κ.W.nL → Bool) : Array Nat :=
  let n := κ.W.nL
  let active : Fin n → Bool := fun l => !decide (IsShared κ l) && !free l
  let deps : Array (List (Fin n)) := (Array.finRange n).map fun l =>
    if active l then (List.finRange n).filter
        (fun b => !decide (IsShared κ b) && depB κ.W l b)
    else []
  let step (lv : Array Nat) : Array Nat := (Array.finRange n).map fun l =>
    if active l then 1 + (deps.getD l.val []).foldl (fun m b => max m (lv.getD b.val 0)) 0
    else 0
  (List.range (n + 1)).foldl (fun lv _ => step lv) (Array.replicate n 0)

/-- Search for the side condition: free latches are the semantic self-resets, levels
    are proposed by `candidateLevels`, and `RespectsFlip` decides whether they work. -/
def findStrat (κ : Witness M) : Option (UnmappedStratification κ) :=
  let free : Fin κ.W.nL → Bool := fun l => decide (SelfReset κ.W l)
  let arr := candidateLevels κ free
  let lvl : Fin κ.W.nL → Nat := fun l => arr.getD l.val 0
  if h : RespectsFlip κ lvl free then
    some { lvl := lvl, free := free,
           free_spec := fun _ hl => of_decide_eq_true hl,
           respects := respects_of_flips h }
  else none

/-! ### The verdict and its soundness -/

/-- One entry per check, and one for the side condition. -/
structure Report where
  strat : Bool
  reset : Bool
  trans : Bool
  prop : Bool
  base : Bool
  step : Bool
deriving Repr

def runChecks (M : SeqCircuit) (κ : Witness M) : Report where
  strat := (findStrat κ).isSome
  reset := decide (ResetCheckKo κ)
  trans := decide (TransCheckKo κ)
  prop := decide (PropertyCheckO κ)
  base := decide (BaseCheck κ)
  step := decide (StepCheckO κ)

/-- All entries pass. -/
def Report.ok (r : Report) : Bool :=
  r.strat && r.reset && r.trans && r.prop && r.base && r.step

/-- **Soundness of the checker.** If every entry of the report passes, the model is
    safe. -/
theorem check_sound (M : SeqCircuit) (κ : Witness M) (h : (runChecks M κ).ok = true) :
    Safe M := by
  simp only [Report.ok, runChecks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hs, hr⟩, ht⟩, hp⟩, hb⟩, hst⟩ := h
  cases hfs : findStrat κ with
  | none => rw [hfs] at hs; simp at hs
  | some st =>
    exact witness_sound_K M κ st (ResetCheckKo.sound (of_decide_eq_true hr))
      (TransCheckKo.sound (of_decide_eq_true ht)) (PropertyCheckO.sound (of_decide_eq_true hp))
      (of_decide_eq_true hb) (StepCheckO.sound (of_decide_eq_true hst))

end KernelCert
