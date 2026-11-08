/-
  KernelCert.Stratification — the reset side condition of the certificate format, the
  reset-existence construction, and relative determinacy.

  FIDELITY. FMCAD'22 (Def. 6) defines the reset-dependency graph with an edge (a, b)
  iff a ∈ vars(r_b) and r_b ≠ b: the self-loop of an UNINITIALIZED latch, which AIGER
  writes as a latch resetting to itself (r_b = b), does not count. A `Stratification`
  renders this semantically: a level `lvl` per latch and a marker `free` for the
  self-reset latches; a marked latch's reset is the identity (`SelfReset`), and an
  unmarked latch's reset value depends only on latches of strictly lower level, for
  every input valuation (`DependsOnlyOnLowerAt`). Reset functions may read inputs.
  Level2.lean generalizes this to the weaker condition Certifaiger has checked since
  version 10.3.0, which also exempts the latches shared with the model.

  PROVED HERE (for each input valuation ι):
  * `resetState_isReset` / `reset_exists`: a stratified circuit has a reset state,
    built by iterating the reset operator; free latches are fixpoints at any value,
    the others stabilize level by level.
  * `reset_unique`: relative determinacy. Two reset states that agree on the free
    (uninitialized) latches are equal. Global uniqueness is false for the format (an
    uninitialized latch resets to either value); it holds when no latch is free
    (`reset_unique_of_grounded`).
-/
import KernelCert.Circuit

namespace KernelCert

/-- `resetVal` at latch `l` depends only on strictly-lower-level latches: for every
    input valuation, two states that agree on all latches below `l`'s level give `l`
    the same reset value. -/
def DependsOnlyOnLowerAt (W : SeqCircuit) (lvl : Fin W.nL → Nat)
    (l : Fin W.nL) : Prop :=
  ∀ (ι : Input W) (s s' : State W),
    (∀ b, lvl b < lvl l → s b = s' b) → W.resetVal ι s l = W.resetVal ι s' l

/-- Every latch's reset value depends only on strictly-lower-level latches: the strict
    form, for circuits with no uninitialized latch. -/
def DependsOnlyOnLower (W : SeqCircuit) (lvl : Fin W.nL → Nat) : Prop :=
  ∀ l, DependsOnlyOnLowerAt W lvl l

/-- Latch `l` resets to itself: the semantic rendering of an UNINITIALIZED latch
    (AIGER's `r_l = l`). Its equation `s l = resetVal ι s l` holds at any value. -/
def SelfReset (W : SeqCircuit) (l : Fin W.nL) : Prop :=
  ∀ (ι : Input W) (s : State W), W.resetVal ι s l = s l

/-- A stratification of `W`'s reset logic, mirroring FMCAD'22 Def. 6: levels on the
    latches and a marker `free` for the self-reset (uninitialized) latches, such that
    every unmarked latch's reset value depends only on strictly-lower latches. -/
structure Stratification (W : SeqCircuit) where
  lvl : Fin W.nL → Nat
  free : Fin W.nL → Bool
  free_spec : ∀ l, free l = true → SelfReset W l
  respects : ∀ l, free l = false → DependsOnlyOnLowerAt W lvl l

/-- `W` is stratified when some level assignment (with self-reset exemptions) works. -/
def Stratified (W : SeqCircuit) : Prop := Nonempty (Stratification W)

/-- The strict special case: levels respected by ALL latches (no uninitialized
    latches) give a stratification with nothing marked free. -/
def Stratification.ofStrict (W : SeqCircuit) (lvl : Fin W.nL → Nat)
    (h : DependsOnlyOnLower W lvl) : Stratification W where
  lvl := lvl
  free := fun _ => false
  free_spec := fun _ hf => Bool.noConfusion hf
  respects := fun l _ => h l

/-! ### Existence: constructing a reset state

  For a fixed input valuation, iterate the reset operator from the all-`false` seed. A
  free latch is a fixed point of its own (identity) reset equation, so it never moves;
  a latch of level `< n` has stabilized after `n` rounds, because its reset value
  reads only strictly-lower latches. The diagonal `l ↦ (lvl l + 1)`-th iterate is
  therefore a reset state. -/

/-- `n`-fold application of the reset operator, under input `ι`, to the all-`false`
    seed. -/
def resetIter (W : SeqCircuit) (ι : Input W) : Nat → State W
  | 0 => fun _ => false
  | n + 1 => fun l => W.resetVal ι (resetIter W ι n) l

/-- One more round does not change a latch whose level is already below `n`. -/
theorem resetIter_stab (W : SeqCircuit) (strat : Stratification W) (ι : Input W) :
    ∀ n, ∀ l, strat.lvl l < n → resetIter W ι (n + 1) l = resetIter W ι n l := by
  intro n
  induction n with
  | zero => intro l h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hl
    cases hf : strat.free l with
    | true =>
      show W.resetVal ι (resetIter W ι (n + 1)) l = resetIter W ι (n + 1) l
      exact strat.free_spec l hf ι (resetIter W ι (n + 1))
    | false =>
      show W.resetVal ι (resetIter W ι (n + 1)) l = W.resetVal ι (resetIter W ι n) l
      apply strat.respects l hf ι
      intro b hb
      apply ih b
      omega

/-- The candidate reset state under input `ι`: each latch reads its stabilized value. -/
def resetState (W : SeqCircuit) (strat : Stratification W) (ι : Input W) : State W :=
  fun l => resetIter W ι (strat.lvl l + 1) l

/-- Every stage strictly past a latch's level agrees with the limit. -/
theorem resetIter_limit (W : SeqCircuit) (strat : Stratification W) (ι : Input W) :
    ∀ n l, strat.lvl l < n → resetIter W ι n l = resetState W strat ι l := by
  intro n
  induction n with
  | zero => intro l h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hl
    by_cases hln : strat.lvl l < n
    · rw [resetIter_stab W strat ι n l hln]
      exact ih l hln
    · have he : strat.lvl l = n := by omega
      show resetIter W ι (n + 1) l = resetIter W ι (strat.lvl l + 1) l
      rw [he]

/-- **Reset existence under stratification**: for every input valuation, the
    level-recursion limit is a reset state. -/
theorem resetState_isReset (W : SeqCircuit) (strat : Stratification W) (ι : Input W) :
    R W ι (resetState W strat ι) := by
  intro l
  cases hf : strat.free l with
  | true => exact (strat.free_spec l hf ι (resetState W strat ι)).symm
  | false =>
    show W.resetVal ι (resetIter W ι (strat.lvl l)) l
        = W.resetVal ι (resetState W strat ι) l
    apply strat.respects l hf ι
    intro b hb
    exact resetIter_limit W strat ι (strat.lvl l) b hb

/-- A stratified circuit has a reset state under every input valuation. -/
theorem reset_exists (W : SeqCircuit) (strat : Stratification W) (ι : Input W) :
    ∃ s : State W, R W ι s :=
  ⟨resetState W strat ι, resetState_isReset W strat ι⟩

/-! ### Relative determinacy

  Global uniqueness of reset states is false for the format: an uninitialized latch
  resets to either value. What holds is relative: under a fixed input, a reset state
  is determined by its values on the free latches. -/

/-- **Relative reset determinacy under stratification**: under a fixed input, two
    reset states that agree on the free (uninitialized) latches are equal. Strong
    induction on level: a free latch is covered by the agreement hypothesis; any other
    latch is determined by strictly-lower latches already shown equal. -/
theorem reset_unique (W : SeqCircuit) (strat : Stratification W) (ι : Input W)
    {s s' : State W}
    (hs  : ∀ l, s  l = W.resetVal ι s  l)
    (hs' : ∀ l, s' l = W.resetVal ι s' l)
    (hfree : ∀ l, strat.free l = true → s l = s' l) :
    s = s' := by
  have aux : ∀ n, ∀ l, strat.lvl l < n → s l = s' l := by
    intro n
    induction n with
    | zero => intro l h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro l hl
      cases hf : strat.free l with
      | true => exact hfree l hf
      | false =>
        by_cases hln : strat.lvl l < n
        · exact ih l hln
        · rw [hs l, hs' l]
          apply strat.respects l hf ι
          intro b hb
          apply ih b
          omega
  funext l
  exact aux (strat.lvl l + 1) l (Nat.lt_succ_self _)

/-- With no free latches (the strict fragment), determinacy is global: under a fixed
    input, a strictly stratified circuit has at most one reset state. -/
theorem reset_unique_of_grounded (W : SeqCircuit) (strat : Stratification W)
    (ι : Input W) (hg : ∀ l, strat.free l = false)
    {s s' : State W}
    (hs  : ∀ l, s  l = W.resetVal ι s  l)
    (hs' : ∀ l, s' l = W.resetVal ι s' l) :
    s = s' :=
  reset_unique W strat ι hs hs'
    (fun l hf => absurd (hf ▸ hg l) (by intro h; exact Bool.noConfusion h))

end KernelCert
