/-
  KernelCert.Level2 — connecting the combinational (K-restricted) checks Certifaiger
  discharges by SAT to the semantic simulation obligations that `witness_sound`
  consumes. BOTH existential bridges are proved.

  PROVED HERE:
  * Transition: the FUNCTIONAL K-restricted transition check implies the semantic
    (existential) `TransitionCheck` obligation. Because the witness's transition is a
    function, the required successor is exactly the one obtained by evaluating `W`'s
    next-state functions on the pre-state; the combinational check certifies precisely
    that this successor's K-projection matches `M` and that `W`'s constraint is
    preserved.
  * Reset: the K-restricted combinational reset check, rendered in the literature's
    exact shape `R↾K ∧ C ⇒ R'↾K ∧ C'` (CAV'25 Def. 1, check (1); `Agree` plays the
    joint-variable identification, private latches universally quantified = free),
    implies the semantic (existential) `ResetCheck` obligation, GIVEN a
    stratification. The proof is the reset-extension construction of CAV'25 Lemma 1
    itself: pin the shared latches to the model reset's values, assign the remaining
    latches level by level (`extendFrom`); free (uninitialized) private latches are
    fixpoints at any value, grounded private latches stabilize by stratification, and
    the check — instantiated at the constructed state — supplies the shared latches'
    reset equations and `C'`.
  * `witness_sound_K`: the composite — soundness with BOTH existential obligations
    derived from their combinational-shape checks rather than assumed.

  The side condition here is `UnmappedStratification`, the condition Certifaiger has
  checked since 10.3.0; the FMCAD'22 condition implies it (`Stratification.toUnmapped`).
-/
import KernelCert.Metatheorem
import KernelCert.Stratification

namespace KernelCert
variable {M : SeqCircuit}

/-- The functional, K-restricted transition check: for the successor obtained by
    evaluating `W`'s next-state functions on the pre-state, its K-projection agrees with
    `M`'s successor and `W`'s constraint is preserved. This is the semantic rendering of
    the shape a combinational Certifaiger transition check certifies (latches as free
    variables, `F'`'s functionality built in rather than existentially asserted). -/
def TransCheckK (κ : Witness M) : Prop :=
  ∀ (ι0 ι1 : Input M) (ιW0 ιW1 : Input κ.W)
    (s0 s1 : State M) (s0' : State κ.W),
    AgreeIn κ ι0 ιW0 → AgreeIn κ ι1 ιW1 → Agree κ s0 s0' →
    F M ι0 s0 s1 → evalC M ι0 s0 = true → evalC M ι1 s1 = true →
    evalC κ.W ιW0 s0' = true →
    (∀ j : Fin κ.k, s1 (κ.embM j) = κ.W.next ιW0 s0' (κ.embW j)) ∧
      evalC κ.W ιW1 (fun l => κ.W.next ιW0 s0' l) = true

/-- **Level-2 transition lemma.** The functional K-restricted transition check implies
    the semantic transition obligation: instantiate the obligation's existential with
    the functional successor `fun l => W.next ιW0 s0' l`. -/
theorem transCheckK_implies_obligation (κ : Witness M) (h : TransCheckK κ) :
    TransitionCheck κ := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' hAI0 hAI1 hag hF hC0 hC1 hC0'
  obtain ⟨hagree, hcons⟩ :=
    h ι0 ι1 ιW0 ιW1 s0 s1 s0' hAI0 hAI1 hag hF hC0 hC1 hC0'
  exact ⟨fun l => κ.W.next ιW0 s0' l, hagree, fun _ => rfl, hcons⟩

/-- The K-restricted combinational reset check, in the literature's exact shape
    `R↾K ∧ C ⇒ R'↾K ∧ C'` (CAV'25 Def. 1, check (1)): over the joint variable space —
    rendered two-sortedly with `Agree` as the shared-latch identification and all
    private latches free (universally quantified) — if `M`'s shared latches satisfy
    their reset equations and `C` holds, then those shared values satisfy `W`'s reset
    equations and `C'` holds. Its negation is a single combinational satisfiability
    query. Note the conclusion asserts the K-restricted reset EQUATIONS of `W` at the
    joint valuation, not the existence of any full reset state; producing that state
    is exactly what the reset-extension construction below adds. -/
def ResetCheckK (κ : Witness M) : Prop :=
  ∀ (ιM : Input M) (ιW : Input κ.W) (sM : State M) (sW : State κ.W),
    AgreeIn κ ιM ιW → Agree κ sM sW →
    (∀ j : Fin κ.k, sM (κ.embM j) = M.resetVal ιM sM (κ.embM j)) →
    evalC M ιM sM = true →
    (∀ j : Fin κ.k, sW (κ.embW j) = κ.W.resetVal ιW sW (κ.embW j)) ∧
      evalC κ.W ιW sW = true

/-- Bounded constructive search for the model reset's value at the shared preimage
    of `l` under `embW`: scan the shared-latch indices below the bound; `none` if
    none matches. The state-side analogue of `liftInputAux` — like it, choice-free,
    because the shared interface is finite and decidably indexed. -/
def sharedVal? (κ : Witness M) (sM : State M) (l : Fin κ.W.nL) : Nat → Option Bool
  | 0 => none
  | j + 1 =>
    if h : j < κ.k then
      if κ.embW ⟨j, h⟩ = l then some (sM (κ.embM ⟨j, h⟩))
      else sharedVal? κ sM l j
    else sharedVal? κ sM l j

/-- The scan finds the shared value (injectivity of `embW` identifies the matching
    index). -/
theorem sharedVal?_shared (κ : Witness M) (sM : State M) (j : Fin κ.k) :
    ∀ b, j.val < b → b ≤ κ.k →
      sharedVal? κ sM (κ.embW j) b = some (sM (κ.embM j)) := by
  intro b
  induction b with
  | zero => intro h _; exact absurd h (Nat.not_lt_zero _)
  | succ c ih =>
    intro hj hb
    have hc : c < κ.k := hb
    show (if h : c < κ.k then
            if κ.embW ⟨c, h⟩ = κ.embW j then some (sM (κ.embM ⟨c, h⟩))
            else sharedVal? κ sM (κ.embW j) c
          else sharedVal? κ sM (κ.embW j) c) = some (sM (κ.embM j))
    rw [dite_eq_left hc]
    by_cases he : κ.embW ⟨c, hc⟩ = κ.embW j
    · rw [ite_eq_left he]
      exact congrArg (fun x => some (sM (κ.embM x))) (κ.embW_inj _ _ he)
    · rw [ite_eq_right he]
      have hne : j.val ≠ c := by
        intro hv
        apply he
        have hj' : (⟨c, hc⟩ : Fin κ.k) = j := Fin.ext hv.symm
        rw [hj']
      apply ih
      · omega
      · omega

/-- On a private latch the scan finds nothing, at any bound. -/
theorem sharedVal?_private (κ : Witness M) (sM : State M) (l : Fin κ.W.nL)
    (hns : ¬ ∃ j : Fin κ.k, κ.embW j = l) :
    ∀ b, sharedVal? κ sM l b = none := by
  intro b
  induction b with
  | zero => rfl
  | succ c ih =>
    show (if h : c < κ.k then
            if κ.embW ⟨c, h⟩ = l then some (sM (κ.embM ⟨c, h⟩))
            else sharedVal? κ sM l c
          else sharedVal? κ sM l c) = none
    by_cases hc : c < κ.k
    · rw [dite_eq_left hc]
      have hne : ¬ κ.embW ⟨c, hc⟩ = l := fun he => hns ⟨⟨c, hc⟩, he⟩
      rw [ite_eq_right hne]
      exact ih
    · rw [dite_eq_right hc]
      exact ih

/-- A successful scan pins the latch as shared. -/
theorem sharedVal?_isSome_shared (κ : Witness M) (sM : State M) (l : Fin κ.W.nL) :
    ∀ b v, sharedVal? κ sM l b = some v → ∃ j : Fin κ.k, κ.embW j = l := by
  intro b
  induction b with
  | zero => intro v h; simp [sharedVal?] at h
  | succ c ih =>
    intro v h
    by_cases hc : c < κ.k
    · by_cases he : κ.embW ⟨c, hc⟩ = l
      · exact ⟨⟨c, hc⟩, he⟩
      · have e : sharedVal? κ sM l (c + 1) = sharedVal? κ sM l c := by
          show (if h : c < κ.k then
                  if κ.embW ⟨c, h⟩ = l then some (sM (κ.embM ⟨c, h⟩))
                  else sharedVal? κ sM l c
                else sharedVal? κ sM l c) = sharedVal? κ sM l c
          rw [dite_eq_left hc, ite_eq_right he]
        exact ih v (e.symm.trans h)
    · have e : sharedVal? κ sM l (c + 1) = sharedVal? κ sM l c := by
        show (if h : c < κ.k then
                if κ.embW ⟨c, h⟩ = l then some (sM (κ.embM ⟨c, h⟩))
                else sharedVal? κ sM l c
              else sharedVal? κ sM l c) = sharedVal? κ sM l c
        rw [dite_eq_right hc]
      exact ih v (e.symm.trans h)

/-- An exhausted scan pins the latch as private. -/
theorem sharedVal?_none_private (κ : Witness M) (sM : State M) (l : Fin κ.W.nL)
    (hn : sharedVal? κ sM l κ.k = none) : ¬ ∃ j : Fin κ.k, κ.embW j = l := by
  intro hex
  obtain ⟨j, hj⟩ := hex
  rw [← hj] at hn
  rw [sharedVal?_shared κ sM j κ.k j.isLt (Nat.le_refl _)] at hn
  cases hn

/-! ### The reset side condition Certifaiger checks since version 10.3.0

  Since version 10.3.0 (2026-09-22, commit 27d526e3) Certifaiger requires a
  stratification only of the witness latches that are not mapped to the model; in
  its own words, "shared witness latches are treated as constants: their reset edges
  are omitted. The Reset check handles the reset equations of mapped latches."
  `UnmappedStratification` is the semantic rendering: levels and free markers as in
  `Stratification`, with the dependency condition imposed on private latches only,
  and a private latch may read any shared latch. Every FMCAD'22 stratification is one
  (`Stratification.toUnmapped`); the converse fails (Examples.lean, `toyW5`). -/

/-- Latch `l` of the witness is shared: some index of `K` maps to it. -/
def IsShared (κ : Witness M) (l : Fin κ.W.nL) : Prop := ∃ j : Fin κ.k, κ.embW j = l

/-- The reset side condition of Certifaiger 10.3.0, semantically: free latches reset to
    themselves, and every private latch that is not free has a reset value that,
    under every input, depends only on latches of strictly lower level and on shared
    latches. Shared latches carry no condition. -/
structure UnmappedStratification (κ : Witness M) where
  lvl : Fin κ.W.nL → Nat
  free : Fin κ.W.nL → Bool
  free_spec : ∀ l, free l = true → SelfReset κ.W l
  respects : ∀ l, ¬ IsShared κ l → free l = false →
    ∀ (ι : Input κ.W) (s s' : State κ.W),
      (∀ b, lvl b < lvl l ∨ IsShared κ b → s b = s' b) →
      κ.W.resetVal ι s l = κ.W.resetVal ι s' l

/-- Every FMCAD'22 stratification of the witness is an unmapped one. -/
def Stratification.toUnmapped (κ : Witness M) (strat : Stratification κ.W) :
    UnmappedStratification κ where
  lvl := strat.lvl
  free := strat.free
  free_spec := strat.free_spec
  respects := fun l _ hf ι s s' h =>
    strat.respects l hf ι s s' (fun b hb => h b (Or.inl hb))

/-- Stage `n` of the reset-extension construction (CAV'25 Lemma 1): shared latches
    are pinned to the model reset's values throughout; private latches start at
    `false` and are re-evaluated through their reset functions each round.
    Computable. -/
def extendFrom (κ : Witness M) (ιW : Input κ.W) (sM : State M) : Nat → State κ.W
  | 0 => fun l => (sharedVal? κ sM l κ.k).getD false
  | n + 1 => fun l =>
    match sharedVal? κ sM l κ.k with
    | some v => v
    | none => κ.W.resetVal ιW (extendFrom κ ιW sM n) l

/-- On a shared latch, every stage carries `M`'s value. -/
theorem extendFrom_shared (κ : Witness M) (ιW : Input κ.W) (sM : State M) (n : Nat)
    (j : Fin κ.k) :
    extendFrom κ ιW sM n (κ.embW j) = sM (κ.embM j) := by
  have hs : sharedVal? κ sM (κ.embW j) κ.k = some (sM (κ.embM j)) :=
    sharedVal?_shared κ sM j κ.k j.isLt (Nat.le_refl _)
  cases n with
  | zero =>
    show (sharedVal? κ sM (κ.embW j) κ.k).getD false = sM (κ.embM j)
    rw [hs]
    rfl
  | succ n =>
    simp only [extendFrom]
    rw [hs]

/-- A free (uninitialized) private latch never moves off the seed value. -/
theorem extendFrom_private_free (κ : Witness M) (strat : UnmappedStratification κ)
    (ιW : Input κ.W) (sM : State M) (l : Fin κ.W.nL)
    (hns : ¬ ∃ j : Fin κ.k, κ.embW j = l) (hf : strat.free l = true) :
    ∀ n, extendFrom κ ιW sM n l = false := by
  have hn : ∀ b, sharedVal? κ sM l b = none := sharedVal?_private κ sM l hns
  intro n
  induction n with
  | zero =>
    show (sharedVal? κ sM l κ.k).getD false = false
    rw [hn]
    rfl
  | succ n ih =>
    simp only [extendFrom]
    rw [hn]
    show κ.W.resetVal ιW (extendFrom κ ιW sM n) l = false
    rw [strat.free_spec l hf ιW (extendFrom κ ιW sM n)]
    exact ih

/-- One more round does not change a latch whose level is already below `n`. -/
theorem extendFrom_stab (κ : Witness M) (strat : UnmappedStratification κ) (ιW : Input κ.W)
    (sM : State M) :
    ∀ n, ∀ l, strat.lvl l < n → extendFrom κ ιW sM (n + 1) l = extendFrom κ ιW sM n l := by
  intro n
  induction n with
  | zero => intro l h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hl
    cases hsv : sharedVal? κ sM l κ.k with
    | some v =>
      obtain ⟨j, hj⟩ := sharedVal?_isSome_shared κ sM l κ.k v hsv
      rw [← hj, extendFrom_shared, extendFrom_shared]
    | none =>
      cases hf : strat.free l with
      | true =>
        have hns := sharedVal?_none_private κ sM l hsv
        rw [extendFrom_private_free κ strat ιW sM l hns hf,
            extendFrom_private_free κ strat ιW sM l hns hf]
      | false =>
        have hns := sharedVal?_none_private κ sM l hsv
        simp only [extendFrom]
        rw [hsv]
        show κ.W.resetVal ιW (extendFrom κ ιW sM (n + 1)) l
            = κ.W.resetVal ιW (extendFrom κ ιW sM n) l
        apply strat.respects l hns hf ιW
        intro b hb
        cases hb with
        | inl hlt => exact ih b (by omega)
        | inr hsh =>
          obtain ⟨j, hj⟩ := hsh
          rw [← hj, extendFrom_shared, extendFrom_shared]

/-- The extension: each latch reads its stabilized value. Computable. -/
def extendState (κ : Witness M) (strat : UnmappedStratification κ) (ιW : Input κ.W)
    (sM : State M) : State κ.W :=
  fun l => extendFrom κ ιW sM (strat.lvl l + 1) l

/-- Every stage strictly past a latch's level agrees with the extension. -/
theorem extendFrom_limit (κ : Witness M) (strat : UnmappedStratification κ) (ιW : Input κ.W)
    (sM : State M) :
    ∀ n l, strat.lvl l < n → extendFrom κ ιW sM n l = extendState κ strat ιW sM l := by
  intro n
  induction n with
  | zero => intro l h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hl
    by_cases hln : strat.lvl l < n
    · rw [extendFrom_stab κ strat ιW sM n l hln]
      exact ih l hln
    · have he : strat.lvl l = n := by omega
      show extendFrom κ ιW sM (n + 1) l = extendFrom κ ιW sM (strat.lvl l + 1) l
      rw [he]

/-- The extension K-agrees with the model reset it was built from, by construction. -/
theorem extendState_agree (κ : Witness M) (strat : UnmappedStratification κ) (ιW : Input κ.W)
    (sM : State M) :
    Agree κ sM (extendState κ strat ιW sM) :=
  fun j => (extendFrom_shared κ ιW sM (strat.lvl (κ.embW j) + 1) j).symm

/-- **Level-2 reset lemma (reset extension).** Under a stratification of the witness,
    the K-restricted combinational reset check implies the semantic reset obligation.
    The extension `extendState` K-agrees with the model reset by construction; its
    private latches satisfy their reset equations by the level recursion (free ones
    trivially, grounded ones by stratification); and the check — instantiated at the
    extension itself — supplies the shared latches' reset equations and `C'`. This is
    the mechanized counterpart of CAV'25 Lemma 1 and of its use in Theorem 1's reset
    step. -/
theorem resetCheckK_implies_obligation (κ : Witness M)
    (strat : UnmappedStratification κ) (h : ResetCheckK κ) :
    ResetCheck κ := by
  intro ιM ιW sM hAI hR hC
  have hag : Agree κ sM (extendState κ strat ιW sM) := extendState_agree κ strat ιW sM
  obtain ⟨hKeq, hC'⟩ :=
    h ιM ιW sM (extendState κ strat ιW sM) hAI hag (fun j => hR (κ.embM j)) hC
  refine ⟨extendState κ strat ιW sM, hag, ?_, hC'⟩
  intro l
  cases hsv : sharedVal? κ sM l κ.k with
  | some v =>
    obtain ⟨j, hj⟩ := sharedVal?_isSome_shared κ sM l κ.k v hsv
    rw [← hj]
    exact hKeq j
  | none =>
    cases hf : strat.free l with
    | true => exact (strat.free_spec l hf ιW (extendState κ strat ιW sM)).symm
    | false =>
      have hns := sharedVal?_none_private κ sM l hsv
      have e : extendState κ strat ιW sM l
          = κ.W.resetVal ιW (extendFrom κ ιW sM (strat.lvl l)) l := by
        show extendFrom κ ιW sM (strat.lvl l + 1) l
            = κ.W.resetVal ιW (extendFrom κ ιW sM (strat.lvl l)) l
        simp only [extendFrom]
        rw [hsv]
      rw [e]
      apply strat.respects l hns hf ιW
      intro b hb
      cases hb with
      | inl hlt => exact extendFrom_limit κ strat ιW sM (strat.lvl l) b hlt
      | inr hsh =>
        obtain ⟨j, hj⟩ := hsh
        rw [← hj]
        show extendFrom κ ιW sM (strat.lvl l) (κ.embW j)
            = extendFrom κ ιW sM (strat.lvl (κ.embW j) + 1) (κ.embW j)
        rw [extendFrom_shared, extendFrom_shared]

/-- **Soundness from the combinational-shape checks.** Under the reset side condition
    Certifaiger checks since version 10.3.0, the two K-restricted checks together with
    the three universal obligations (whose combinational forms have the same shape)
    imply safety: `witness_sound` with both existential obligations derived rather than
    assumed. This is the semantic form of the format's soundness statement. -/
theorem witness_sound_K
    (M : SeqCircuit) (κ : Witness M) (strat : UnmappedStratification κ)
    (h1 : ResetCheckK κ) (h2 : TransCheckK κ) (h3 : PropertyCheck κ)
    (h4 : BaseCheck κ) (h5 : StepCheck κ) :
    Safe M :=
  witness_sound M κ (resetCheckK_implies_obligation κ strat h1)
    (transCheckK_implies_obligation κ h2) h3 h4 h5

/-- The same under the FMCAD'22 side condition (all witness latches stratified), the
    condition Certifaiger checked before version 10.3.0. -/
theorem witness_sound_K_of_stratification
    (M : SeqCircuit) (κ : Witness M) (strat : Stratification κ.W)
    (h1 : ResetCheckK κ) (h2 : TransCheckK κ) (h3 : PropertyCheck κ)
    (h4 : BaseCheck κ) (h5 : StepCheck κ) :
    Safe M :=
  witness_sound_K M κ (Stratification.toUnmapped κ strat) h1 h2 h3 h4 h5

end KernelCert
