/-
  KernelCert.Examples: worked instances.

  * `toy_safe`: a circuit certified by itself.
  * `toy2_safe`, `toy2_safe_K`: a witness with a private latch.
  * `toy3_safe`, `toy3_safe_K`: a real input, a constraint the proof needs, and a witness
    invariant that strengthens a property that is not 1-inductive (`toy3_P_not_inductive`).
  * `toy4_safe`: an uninitialized model latch (two reset states).
  * `toyW5_not_stratified`, `toy5_safe_K`: a witness whose shared latch resets to `k ∧ p`;
    no FMCAD'22 stratification exists, the 10.3.0 condition holds, the model is safe.
  * `toy6_safe_K`: reset values that read an input.
-/
import KernelCert.Metatheorem
import KernelCert.Stratification
import KernelCert.Level2

namespace KernelCert
namespace Examples

/-! ### A self-certifying instance -/

/-- One latch, resets to `false`, next-state constantly `false`, property "latch is
    low", no inputs, constraint `true`. -/
def toyM : SeqCircuit where
  nI := 0
  nL := 1
  resetVal := fun _ _ _ => false
  next := fun _ _ _ => false
  good := fun _ s => !(s 0)
  cons := fun _ _ => true

/-- The canonical (only) latch index, written once so that the `toyW` proofs below use
    the same term (numeral-instance search does not see through `toyW.W.nL`). -/
private def z : Fin 1 := 0

/-- `toyM` certified by itself: `W = M`, `K` = the full (one-element) latch set,
    no shared inputs (`toyM` has none). -/
def toyW : Witness toyM where
  W := toyM
  k := 1
  embM := fun j => j
  embW := fun j => j
  embM_inj := fun _ _ h => h
  embW_inj := fun _ _ h => h
  kIn := 0
  inM := fun j => j.elim0
  inW := fun j => j.elim0
  inM_inj := fun a => a.elim0
  inW_inj := fun a => a.elim0

theorem toy_reset : ResetCheck toyW := by
  intro ιM ιW sM _hAI hR _hC
  exact ⟨sM, fun _ => rfl, hR, rfl⟩

theorem toy_trans : TransitionCheck toyW := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' _hAI0 _hAI1 _hag hF _hC0 _hC1 _hC0'
  refine ⟨s1, fun _ => rfl, ?_, rfl⟩
  -- `F toyM ιW0 s0' s1` demands each post-latch equal the (constantly false)
  -- next-state function; `hF` already pins `s1` to false.
  intro l
  exact hF l

theorem toy_prop : PropertyCheck toyW := by
  intro ιM ιW sM sW _hAI hag _hCM _hCW hP
  have h0 : sM z = sW z := hag z
  show (!(sM z)) = true
  rw [h0]
  exact hP

theorem toy_base : BaseCheck toyW := by
  intro ιW sW hR _hC
  have h : sW z = false := hR z
  show (!(sW z)) = true
  rw [h]
  rfl

theorem toy_step : StepCheck toyW := by
  intro ι0 ι1 s0' s1' _hP hF _hC0 _hC1
  have h : s1' z = false := hF z
  show (!(s1' z)) = true
  rw [h]
  rfl

/-- End to end: the five concrete obligations composed by the metatheorem into safety
    of a concrete circuit. Sorry-free; standard axioms only. -/
theorem toy_safe : Safe toyM :=
  witness_sound toyM toyW toy_reset toy_trans toy_prop toy_base toy_step

/-- `toyW` is (trivially) stratified: all resets are constant, so any level assignment
    is respected and no latch is uninitialized. -/
def toyW_strat : Stratification toyW.W where
  lvl := fun _ => 0
  free := fun _ => false
  free_spec := fun _ hf => Bool.noConfusion hf
  respects := fun _ _ _ _ _ _ => rfl

example : Stratified toyW.W := ⟨toyW_strat⟩

/-- Relative reset determinacy is usable on a concrete stratified witness (with no
    free latches, the agreement hypothesis is vacuous and determinacy is global). -/
example (ι : Input toyW.W) (s s' : State toyW.W)
    (hs : ∀ l, s l = toyW.W.resetVal ι s l) (hs' : ∀ l, s' l = toyW.W.resetVal ι s' l) :
    s = s' :=
  reset_unique toyW.W toyW_strat ι hs hs' (fun _ hf => Bool.noConfusion hf)

/-! ### A non-degenerate witness with a private (non-shared) latch

  This mechanically confirms that the existential obligations ARE satisfiable for a
  witness whose latch set strictly extends `K`, the case in which the
  universal-conclusion forms are unsatisfiable (mechanized refutation:
  KernelCert/Counterexamples.lean). `toyW2W` has two latches; only latch 0 is shared
  with `M` (via the embeddings below), latch 1 is private. -/

/-- The witness circuit with a private auxiliary latch (latch 1). -/
def toyW2W : SeqCircuit where
  nI := 0
  nL := 2
  resetVal := fun _ _ _ => false
  next := fun _ _ _ => false
  good := fun _ s => !(s 0)
  cons := fun _ _ => true

/-- `toyM` certified by a witness with an extra private latch. `K = {latch 0}`;
    latch 1 of `toyW2W` is outside `K`. -/
def toyW2 : Witness toyM where
  W := toyW2W
  k := 1
  embM := fun j => j
  embW := fun _ => (0 : Fin 2)
  embM_inj := fun _ _ h => h
  embW_inj := fun a b _ => by
    have := a.isLt; have := b.isLt; exact Fin.ext (by omega)
  kIn := 0
  inM := fun j => j.elim0
  inW := fun j => j.elim0
  inM_inj := fun a => a.elim0
  inW_inj := fun a => a.elim0

theorem toy2_reset : ResetCheck toyW2 := by
  intro ιM ιW sM _hAI hR _hC
  refine ⟨fun _ => false, ?_, ?_, rfl⟩
  · intro j; exact hR (toyW2.embM j)
  · intro _; rfl

theorem toy2_trans : TransitionCheck toyW2 := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' _hAI0 _hAI1 _hag hF _hC0 _hC1 _hC0'
  refine ⟨fun _ => false, ?_, ?_, rfl⟩
  · intro j; exact hF (toyW2.embM j)
  · intro _; rfl

theorem toy2_prop : PropertyCheck toyW2 := by
  intro ιM ιW sM sW _hAI hag _hCM _hCW hP
  have h0 : sM (0 : Fin 1) = sW (0 : Fin 2) := hag (0 : Fin 1)
  show (!(sM (0 : Fin 1))) = true
  rw [h0]; exact hP

theorem toy2_base : BaseCheck toyW2 := by
  intro ιW sW hR _hC
  have h : sW (0 : Fin 2) = false := hR (0 : Fin 2)
  show (!(sW (0 : Fin 2))) = true
  rw [h]; rfl

theorem toy2_step : StepCheck toyW2 := by
  intro ι0 ι1 s0' s1' _hP hF _hC0 _hC1
  have h : s1' (0 : Fin 2) = false := hF (0 : Fin 2)
  show (!(s1' (0 : Fin 2))) = true
  rw [h]; rfl

/-- End to end with a private auxiliary latch: the existential obligations compose into
    safety. Sorry-free; standard axioms only. -/
theorem toy2_safe : Safe toyM :=
  witness_sound toyM toyW2 toy2_reset toy2_trans toy2_prop toy2_base toy2_step

/-- The aux-latch witness is stratified too. -/
def toyW2_strat : Stratification toyW2.W where
  lvl := fun _ => 0
  free := fun _ => false
  free_spec := fun _ hf => Bool.noConfusion hf
  respects := fun _ _ _ _ _ _ => rfl

/-! #### Through Level 2

  The same aux-latch instance, certified from the K-restricted checks instead of the
  semantic obligations: `ResetCheckK`/`TransCheckK` are discharged for the concrete
  circuits, and `witness_sound_K` (with the stratification above) composes them into
  `Safe toyM` — exercising the reset-extension construction on the way. -/

theorem toy2_resetK : ResetCheckK toyW2 := by
  intro ιM ιW sM sW _hAI hag hRK _hC
  constructor
  · intro j
    have h1 : sM (toyW2.embM j) = false := hRK j
    have h2 : sW (toyW2.embW j) = false := (hag j).symm.trans h1
    exact h2
  · rfl

theorem toy2_transK : TransCheckK toyW2 := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' _hAI0 _hAI1 _hag hF _hC0 _hC1 _hC0'
  constructor
  · intro j
    exact hF (toyW2.embM j)
  · rfl

/-- End to end THROUGH LEVEL 2 with a private auxiliary latch: the K-restricted reset
    and transition checks compose, via the reset-extension construction and
    `witness_sound_K`, into safety. Sorry-free; standard axioms only. -/
theorem toy2_safe_K : Safe toyM :=
  witness_sound_K_of_stratification toyM toyW2 toyW2_strat
    toy2_resetK toy2_transK toy2_prop toy2_base toy2_step

/-! ### An instance with inputs, a load-bearing constraint, and genuine strengthening

  Latches `x` (index 0) and `y` (index 1), one input `i`. Reset: both `false`.
  Dynamics: `x' = y ∨ ¬i`, `y' = x ∧ i`. Property `P = ¬x`; constraint `C = i`.
  Under the constraint every constrained run keeps both latches low; without it, the
  very first step raises `x`, so the constraint is load-bearing for safety. `P` alone
  is not 1-inductive (mechanized refutation below): from the `P`-and-`C`-satisfying
  configuration `x = 0, y = 1, i = 1` one constrained step reaches `x = 1`. The
  witness certifies safety by the STRENGTHENED 1-inductive invariant
  `P' = ¬x ∧ ¬y`. -/

def toyM3 : SeqCircuit where
  nI := 1
  nL := 2
  resetVal := fun _ _ _ => false
  next := fun ι s l => if l.val = 0 then (s 1 || !(ι 0)) else (s 0 && ι 0)
  good := fun _ s => !(s 0)
  cons := fun ι _ => ι 0

/-- The witness circuit: same interface and dynamics, strengthened property
    `P' = ¬x ∧ ¬y`. -/
def toyW3W : SeqCircuit where
  nI := 1
  nL := 2
  resetVal := fun _ _ _ => false
  next := fun ι s l => if l.val = 0 then (s 1 || !(ι 0)) else (s 0 && ι 0)
  good := fun _ s => !(s 0) && !(s 1)
  cons := fun ι _ => ι 0

/-- Both latches and the input are shared (identity embeddings). -/
def toyW3 : Witness toyM3 where
  W := toyW3W
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

/-- `P = ¬x` alone is NOT 1-inductive for `toyM3` under its constraint: consecution
    fails from `x = 0, y = 1, i = 1`. The strengthening `P'` carried by the witness
    is genuinely needed. -/
theorem toy3_P_not_inductive :
    ¬ (∀ (ι0 ι1 : Input toyM3) (s0 s1 : State toyM3),
        evalP toyM3 ι0 s0 = true → evalC toyM3 ι0 s0 = true →
        evalC toyM3 ι1 s1 = true → F toyM3 ι0 s0 s1 →
        evalP toyM3 ι1 s1 = true) := by
  intro h
  have hbad := h (fun _ => true) (fun _ => true)
      (fun l => if l.val = 0 then false else true)
      (fun l => toyM3.next (fun _ => true)
        (fun l => if l.val = 0 then false else true) l)
      rfl rfl rfl (fun _ => rfl)
  exact Bool.noConfusion hbad

theorem toy3_reset : ResetCheck toyW3 := by
  intro ιM ιW sM hAI hR hC
  refine ⟨fun _ => false, ?_, ?_, ?_⟩
  · intro j
    exact hR (toyW3.embM j)
  · intro _; rfl
  · -- `C' = i` at the witness: from the shared-input identification and `C = i`
    have h0 : ιM (0 : Fin 1) = ιW (0 : Fin 1) := hAI (0 : Fin 1)
    show ιW (0 : Fin 1) = true
    rw [← h0]
    exact hC

theorem toy3_trans : TransitionCheck toyW3 := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' hAI0 hAI1 hag hF hC0 hC1 hC0'
  have hi0 : ι0 (0 : Fin 1) = ιW0 (0 : Fin 1) := hAI0 (0 : Fin 1)
  have hi1 : ι1 (0 : Fin 1) = ιW1 (0 : Fin 1) := hAI1 (0 : Fin 1)
  refine ⟨fun l => toyW3W.next ιW0 s0' l, ?_, fun _ => rfl, ?_⟩
  · intro j
    have h := hF (toyW3.embM j)
    rw [h]
    show (if j.val = 0 then (s0 (1 : Fin 2) || !(ι0 (0 : Fin 1)))
          else (s0 (0 : Fin 2) && ι0 (0 : Fin 1)))
        = (if j.val = 0 then (s0' (1 : Fin 2) || !(ιW0 (0 : Fin 1)))
          else (s0' (0 : Fin 2) && ιW0 (0 : Fin 1)))
    have e0 : s0 (0 : Fin 2) = s0' (0 : Fin 2) := hag (0 : Fin 2)
    have e1 : s0 (1 : Fin 2) = s0' (1 : Fin 2) := hag (1 : Fin 2)
    rw [e0, e1, hi0]
  · show ιW1 (0 : Fin 1) = true
    rw [← hi1]
    exact hC1

theorem toy3_prop : PropertyCheck toyW3 := by
  intro ιM ιW sM sW _hAI hag _hCM _hCW hP
  have h0 : sM (0 : Fin 2) = sW (0 : Fin 2) := hag (0 : Fin 2)
  have h' : (!(sW (0 : Fin 2)) && !(sW (1 : Fin 2))) = true := hP
  show (!(sM (0 : Fin 2))) = true
  rw [h0]
  cases hx : sW (0 : Fin 2) with
  | false => rfl
  | true => rw [hx] at h'; exact Bool.noConfusion h'

theorem toy3_base : BaseCheck toyW3 := by
  intro ιW sW hR _hC
  have h0 : sW (0 : Fin 2) = false := hR (0 : Fin 2)
  have h1 : sW (1 : Fin 2) = false := hR (1 : Fin 2)
  show (!(sW (0 : Fin 2)) && !(sW (1 : Fin 2))) = true
  rw [h0, h1]
  rfl

theorem toy3_step : StepCheck toyW3 := by
  intro ι0 ι1 s0' s1' hP hF hC0 _hC1
  -- the constraint pins the pre-frame input high; `P'` then propagates
  have hi : ι0 (0 : Fin 1) = true := hC0
  have hP0 : (!(s0' (0 : Fin 2)) && !(s0' (1 : Fin 2))) = true := hP
  have hx : s0' (0 : Fin 2) = false := by
    cases h : s0' (0 : Fin 2) with
    | false => rfl
    | true => rw [h] at hP0; exact Bool.noConfusion hP0
  have hy : s0' (1 : Fin 2) = false := by
    cases h : s0' (1 : Fin 2) with
    | false => rfl
    | true => rw [hx, h] at hP0; exact Bool.noConfusion hP0
  have e0 : s1' (0 : Fin 2) = false := by
    have h := hF (0 : Fin 2)
    rw [h]
    show (s0' (1 : Fin 2) || !(ι0 (0 : Fin 1))) = false
    rw [hy, hi]
    rfl
  have e1 : s1' (1 : Fin 2) = false := by
    have h := hF (1 : Fin 2)
    rw [h]
    show (s0' (0 : Fin 2) && ι0 (0 : Fin 1)) = false
    rw [hx]
    rfl
  show (!(s1' (0 : Fin 2)) && !(s1' (1 : Fin 2))) = true
  rw [e0, e1]
  rfl

/-- End to end with a real input, a load-bearing constraint, and a strengthened
    invariant. Sorry-free; standard axioms only. -/
theorem toy3_safe : Safe toyM3 :=
  witness_sound toyM3 toyW3 toy3_reset toy3_trans toy3_prop toy3_base toy3_step

def toy3_strat : Stratification toyW3.W where
  lvl := fun _ => 0
  free := fun _ => false
  free_spec := fun _ hf => Bool.noConfusion hf
  respects := fun _ _ _ _ _ _ => rfl

theorem toy3_resetK : ResetCheckK toyW3 := by
  intro ιM ιW sM sW hAI hag hRK hC
  constructor
  · intro j
    have h1 : sM (toyW3.embM j) = false := hRK j
    have h2 : sW (toyW3.embW j) = false := (hag j).symm.trans h1
    exact h2
  · have h0 : ιM (0 : Fin 1) = ιW (0 : Fin 1) := hAI (0 : Fin 1)
    show ιW (0 : Fin 1) = true
    rw [← h0]
    exact hC

theorem toy3_transK : TransCheckK toyW3 := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' hAI0 hAI1 hag hF hC0 hC1 hC0'
  have hi0 : ι0 (0 : Fin 1) = ιW0 (0 : Fin 1) := hAI0 (0 : Fin 1)
  have hi1 : ι1 (0 : Fin 1) = ιW1 (0 : Fin 1) := hAI1 (0 : Fin 1)
  constructor
  · intro j
    have h := hF (toyW3.embM j)
    rw [h]
    show (if j.val = 0 then (s0 (1 : Fin 2) || !(ι0 (0 : Fin 1)))
          else (s0 (0 : Fin 2) && ι0 (0 : Fin 1)))
        = (if j.val = 0 then (s0' (1 : Fin 2) || !(ιW0 (0 : Fin 1)))
          else (s0' (0 : Fin 2) && ιW0 (0 : Fin 1)))
    have e0 : s0 (0 : Fin 2) = s0' (0 : Fin 2) := hag (0 : Fin 2)
    have e1 : s0 (1 : Fin 2) = s0' (1 : Fin 2) := hag (1 : Fin 2)
    rw [e0, e1, hi0]
  · show ιW1 (0 : Fin 1) = true
    rw [← hi1]
    exact hC1

/-- The strengthening instance through Level 2. Sorry-free; standard axioms only. -/
theorem toy3_safe_K : Safe toyM3 :=
  witness_sound_K_of_stratification toyM3 toyW3 toy3_strat
    toy3_resetK toy3_transK toy3_prop toy3_base toy3_step

/-! ### An instance with an uninitialized latch

  Latch 0 (`y`) resets to `false`; latch 1 (`x`) is UNINITIALIZED — its reset is the
  identity, AIGER's `r_l = l` encoding of an undefined reset value — so the circuit
  has TWO reset states and global reset determinacy genuinely fails. Dynamics:
  every latch's next value is `y`; property `P = ¬y`; no inputs. -/

def toyM4 : SeqCircuit where
  nI := 0
  nL := 2
  resetVal := fun _ s l => if l.val = 0 then false else s l
  next := fun _ s _ => s 0
  good := fun _ s => !(s 0)
  cons := fun _ _ => true

/-- `toyM4` certified by itself (full sharing). -/
def toyW4 : Witness toyM4 where
  W := toyM4
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

/-- Both truth values of the uninitialized latch give a reset state: the all-`false`
    state is a reset... -/
example (ι : Input toyM4) : R toyM4 ι (fun _ => false) := by
  intro l
  by_cases h : l.val = 0
  · show (false : Bool) = (if l.val = 0 then false else false)
    rw [ite_eq_left h]
  · show (false : Bool) = (if l.val = 0 then false else false)
    rw [ite_eq_right h]

/-- ...and so is the state with the uninitialized latch high: global reset
    determinacy fails for circuits with uninitialized latches. -/
example (ι : Input toyM4) : R toyM4 ι (fun l => if l.val = 0 then false else true) := by
  intro l
  by_cases h : l.val = 0
  · rw [show toyM4.resetVal ι (fun l => if l.val = 0 then false else true) l
        = false from ite_eq_left h]
    exact ite_eq_left h
  · rw [show toyM4.resetVal ι (fun l => if l.val = 0 then false else true) l
        = (if l.val = 0 then false else true) from ite_eq_right h]

/-- The stratification marks the uninitialized latch `free` — the semantic rendering
    of FMCAD'22 Def. 6's `r_b ≠ b` self-loop exemption. -/
def toyW4_strat : Stratification toyW4.W where
  lvl := fun _ => 0
  free := fun l => if l.val = 0 then false else true
  free_spec := by
    intro l hf _ s
    have hf' : (if l.val = 0 then false else true) = true := hf
    by_cases h : l.val = 0
    · rw [ite_eq_left h] at hf'
      exact Bool.noConfusion hf'
    · show (if l.val = 0 then false else s l) = s l
      rw [ite_eq_right h]
  respects := by
    intro l hf _ s s' _
    have hf' : (if l.val = 0 then false else true) = false := hf
    by_cases h : l.val = 0
    · show (if l.val = 0 then false else s l) = (if l.val = 0 then false else s' l)
      rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h] at hf'
      exact Bool.noConfusion hf'

/-- RELATIVE determinacy in action: any two resets of `toyM4` that agree on the
    uninitialized latch are equal. -/
example (ι : Input toyM4) (s s' : State toyM4)
    (hs : ∀ l, s l = toyM4.resetVal ι s l) (hs' : ∀ l, s' l = toyM4.resetVal ι s' l)
    (hfree : s (1 : Fin 2) = s' (1 : Fin 2)) : s = s' :=
  reset_unique toyM4 toyW4_strat ι hs hs' (by
    intro l hf
    by_cases h : l.val = 0
    · rw [show toyW4_strat.free l = false from ite_eq_left h] at hf
      exact Bool.noConfusion hf
    · have hl : l = (1 : Fin 2) := by
        have hlt : l.val < 2 := l.isLt
        have hv : l.val = 1 := by omega
        exact Fin.ext (by rw [hv]; rfl)
      rw [hl]
      exact hfree)

theorem toy4_reset : ResetCheck toyW4 := by
  intro ιM ιW sM _hAI hR _hC
  exact ⟨sM, fun _ => rfl, hR, rfl⟩

theorem toy4_trans : TransitionCheck toyW4 := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' _hAI0 _hAI1 hag hF _hC0 _hC1 _hC0'
  refine ⟨fun l => toyM4.next ιW0 s0' l, ?_, fun _ => rfl, rfl⟩
  intro j
  have h := hF (toyW4.embM j)
  rw [h]
  show s0 (0 : Fin 2) = s0' (0 : Fin 2)
  exact hag (0 : Fin 2)

theorem toy4_prop : PropertyCheck toyW4 := by
  intro ιM ιW sM sW _hAI hag _hCM _hCW hP
  have h0 : sM (0 : Fin 2) = sW (0 : Fin 2) := hag (0 : Fin 2)
  show (!(sM (0 : Fin 2))) = true
  rw [h0]
  exact hP

theorem toy4_base : BaseCheck toyW4 := by
  intro ιW sW hR _hC
  have h : sW (0 : Fin 2) = false := hR (0 : Fin 2)
  show (!(sW (0 : Fin 2))) = true
  rw [h]
  rfl

theorem toy4_step : StepCheck toyW4 := by
  intro ι0 ι1 s0' s1' hP hF _hC0 _hC1
  have h := hF (0 : Fin 2)
  show (!(s1' (0 : Fin 2))) = true
  rw [h]
  exact hP

/-- End to end with an uninitialized model latch. Sorry-free; standard axioms only. -/
theorem toy4_safe : Safe toyM4 :=
  witness_sound toyM4 toyW4 toy4_reset toy4_trans toy4_prop toy4_base toy4_step

/-! ### A witness only the 10.3.0 side condition admits

  Model: one latch `m`, reset low, holding its value; bad = `m`. Witness: latch 0 `k`,
  shared with `m`, and latch 1 `p`, private. `k` resets to `k ∧ p`, a reset that reads
  `k` itself and a private latch; `p` resets low; both hold their values. No FMCAD'22
  stratification exists (`toyW5_not_stratified`), so Certifaiger before 10.3.0 rejects
  the witness ("Witness resets not stratified"); the unmapped-only condition holds, and
  `witness_sound_K` proves the model safe from it. -/

def toyM5 : SeqCircuit where
  nI := 0
  nL := 1
  resetVal := fun _ _ _ => false
  next := fun _ s l => s l
  good := fun _ s => !(s 0)
  cons := fun _ _ => true

def toyW5W : SeqCircuit where
  nI := 0
  nL := 2
  resetVal := fun _ s l => if l.val = 0 then (s 0 && s 1) else false
  next := fun _ s l => s l
  good := fun _ s => !(s 0)
  cons := fun _ _ => true

def toyW5 : Witness toyM5 where
  W := toyW5W
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

/-- No FMCAD'22 stratification exists: `k`'s reset depends on `k` itself. -/
theorem toyW5_not_stratified : ¬ Stratified toyW5.W := by
  intro ⟨strat⟩
  cases hf : strat.free (0 : Fin 2) with
  | true =>
    have h := strat.free_spec (0 : Fin 2) hf (fun i => i.elim0) (fun l => decide (l.val = 0))
    exact Bool.noConfusion h
  | false =>
    have h := strat.respects (0 : Fin 2) hf (fun i => i.elim0)
      (fun _ => true) (fun l => decide (l.val ≠ 0)) (by
        intro b hb
        by_cases hb0 : b.val = 0
        · have hb' : b = (0 : Fin 2) := Fin.ext hb0
          rw [hb'] at hb
          exact absurd hb (Nat.lt_irrefl _)
        · show true = decide (b.val ≠ 0)
          simp [hb0])
    exact Bool.noConfusion h

/-- The unmapped-only condition holds: the private latch `p` resets to a constant. -/
def toy5_ustrat : UnmappedStratification toyW5 where
  lvl := fun _ => 0
  free := fun _ => false
  free_spec := fun _ hf => Bool.noConfusion hf
  respects := by
    intro l hns _ ι s s' _
    have hl : l.val ≠ 0 := by
      intro h0
      exact hns ⟨⟨0, by decide⟩, Fin.ext h0.symm⟩
    show (if l.val = 0 then (s (0 : Fin 2) && s (1 : Fin 2)) else false)
        = (if l.val = 0 then (s' (0 : Fin 2) && s' (1 : Fin 2)) else false)
    rw [ite_eq_right hl, ite_eq_right hl]

theorem toy5_resetK : ResetCheckK toyW5 := by
  intro ιM ιW sM sW _hAI hag hRK _hC
  refine ⟨?_, rfl⟩
  intro j
  have h1 : sM j = false := hRK j
  have h2 : sM j = sW (0 : Fin 2) := hag j
  have h0 : sW (0 : Fin 2) = false := h2.symm.trans h1
  show sW (0 : Fin 2) = (if (0 : Fin 2).val = 0 then (sW (0 : Fin 2) && sW (1 : Fin 2)) else false)
  rw [h0]
  rfl

theorem toy5_transK : TransCheckK toyW5 := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' _hAI0 _hAI1 hag hF _hC0 _hC1 _hC0'
  refine ⟨?_, rfl⟩
  intro j
  rw [hF (toyW5.embM j)]
  exact hag j

theorem toy5_prop : PropertyCheck toyW5 := by
  intro ιM ιW sM sW _hAI hag _hCM _hCW hP
  have e : sM (0 : Fin 1) = sW (0 : Fin 2) := hag (0 : Fin 1)
  show (!(sM (0 : Fin 1))) = true
  rw [e]
  exact hP

theorem toy5_base : BaseCheck toyW5 := by
  intro ιW sW hR _hC
  have h1 : sW (1 : Fin 2) = false := hR (1 : Fin 2)
  have h0 : sW (0 : Fin 2) = (sW (0 : Fin 2) && sW (1 : Fin 2)) := hR (0 : Fin 2)
  rw [h1, Bool.and_false] at h0
  show (!(sW (0 : Fin 2))) = true
  rw [h0]
  rfl

theorem toy5_step : StepCheck toyW5 := by
  intro ι0 ι1 s0' s1' hP hF _hC0 _hC1
  show (!(s1' (0 : Fin 2))) = true
  rw [hF (0 : Fin 2)]
  exact hP

theorem toy5_safe_K : Safe toyM5 :=
  witness_sound_K toyM5 toyW5 toy5_ustrat toy5_resetK toy5_transK toy5_prop toy5_base toy5_step

/-! ### An instance whose resets read an input

  Two latches `x` (index 0) and `y` (index 1) and one input `i`. Reset: `x` takes
  the current input, `y` its negation, so the reset states depend on the input at
  time 0, which Certifaiger's format and the 2026 formulation (`r_l(I, L)`) allow.
  Dynamics: the latches swap. Property `P = x ≠ y`. The circuit certifies itself,
  latches and input shared. -/

def toyM6 : SeqCircuit where
  nI := 1
  nL := 2
  resetVal := fun ι _ l => if l.val = 0 then ι 0 else !(ι 0)
  next := fun _ s l => if l.val = 0 then s 1 else s 0
  good := fun _ s => (s 0 != s 1)
  cons := fun _ _ => true

/-- `toyM6` certified by itself: both latches and the input shared. -/
def toyW6 : Witness toyM6 where
  W := toyM6
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

/-- The reset values read no latch, so every latch sits at level 0. -/
def toy6_strat : Stratification toyW6.W where
  lvl := fun _ => 0
  free := fun _ => false
  free_spec := fun _ hf => Bool.noConfusion hf
  respects := fun _ _ _ _ _ _ => rfl

/-- The reset state exists for every value of the input, and it moves with it. -/
example (ι : Input toyM6) : ∃ s, R toyM6 ι s := reset_exists toyM6 toy6_strat ι

theorem toy6_resetK : ResetCheckK toyW6 := by
  intro ιM ιW sM sW hAI hag hRK _hC
  have hi : ιM (0 : Fin 1) = ιW (0 : Fin 1) := hAI (0 : Fin 1)
  refine ⟨?_, rfl⟩
  intro j
  have h2 : sM j = sW j := hag j
  have h1 : sM j = (if j.val = 0 then ιM (0 : Fin 1) else !(ιM (0 : Fin 1))) := hRK j
  show sW j = (if j.val = 0 then ιW (0 : Fin 1) else !(ιW (0 : Fin 1)))
  rw [← h2, h1, hi]

theorem toy6_transK : TransCheckK toyW6 := by
  intro ι0 ι1 ιW0 ιW1 s0 s1 s0' _hAI0 _hAI1 hag hF _hC0 _hC1 _hC0'
  refine ⟨?_, rfl⟩
  intro j
  have h := hF (toyW6.embM j)
  rw [h]
  show (if j.val = 0 then s0 (1 : Fin 2) else s0 (0 : Fin 2))
      = (if j.val = 0 then s0' (1 : Fin 2) else s0' (0 : Fin 2))
  have e0 : s0 (0 : Fin 2) = s0' (0 : Fin 2) := hag (0 : Fin 2)
  have e1 : s0 (1 : Fin 2) = s0' (1 : Fin 2) := hag (1 : Fin 2)
  rw [e0, e1]

theorem toy6_prop : PropertyCheck toyW6 := by
  intro ιM ιW sM sW _hAI hag _hCM _hCW hP
  have e0 : sM (0 : Fin 2) = sW (0 : Fin 2) := hag (0 : Fin 2)
  have e1 : sM (1 : Fin 2) = sW (1 : Fin 2) := hag (1 : Fin 2)
  show (sM (0 : Fin 2) != sM (1 : Fin 2)) = true
  rw [e0, e1]
  exact hP

theorem toy6_base : BaseCheck toyW6 := by
  intro ιW sW hR _hC
  have h0 : sW (0 : Fin 2) = ιW (0 : Fin 1) := hR (0 : Fin 2)
  have h1 : sW (1 : Fin 2) = !(ιW (0 : Fin 1)) := hR (1 : Fin 2)
  show (sW (0 : Fin 2) != sW (1 : Fin 2)) = true
  rw [h0, h1]
  cases ιW (0 : Fin 1) <;> rfl

theorem toy6_step : StepCheck toyW6 := by
  intro ι0 ι1 s0' s1' hP hF _hC0 _hC1
  have h0 : s1' (0 : Fin 2) = s0' (1 : Fin 2) := hF (0 : Fin 2)
  have h1 : s1' (1 : Fin 2) = s0' (0 : Fin 2) := hF (1 : Fin 2)
  have hP0 : (s0' (0 : Fin 2) != s0' (1 : Fin 2)) = true := hP
  show (s1' (0 : Fin 2) != s1' (1 : Fin 2)) = true
  rw [h0, h1]
  revert hP0
  cases s0' (0 : Fin 2) <;> cases s0' (1 : Fin 2) <;> exact id

/-- End to end through Level 2 with input-dependent resets. Sorry-free. -/
theorem toy6_safe_K : Safe toyM6 :=
  witness_sound_K_of_stratification toyM6 toyW6 toy6_strat
    toy6_resetK toy6_transK toy6_prop toy6_base toy6_step

end Examples
end KernelCert
