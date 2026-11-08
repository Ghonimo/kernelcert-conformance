/-
  KernelCert.Circuit — the sequential-circuit model and constrained-trace safety.

  The reset, transition, property and constraint predicates are given semantically,
  as Lean functions, rather than as denotations of an and-inverter graph;
  KernelCert/Aig.lean instantiates them from a parsed AIGER file. Reset functions may
  read the current inputs as well as the latches: Certifaiger's input format lets a
  latch reset to any literal, and the 2026 formulation of the certificate format
  writes reset functions as `r_l(I, L)`.
-/
namespace KernelCert

/-- A bit-level sequential circuit `M = (I, L, R, F, P, C)`.
    `resetVal`, `next`, `good`, `cons` stand for the reset functions, the next-state
    functions, the good-states predicate `P`, and the constraint `C`. -/
structure SeqCircuit where
  /-- number of ordered inputs `I`. -/
  nI : Nat
  /-- number of ordered latches `L`. -/
  nL : Nat
  /-- per-latch reset value, as a function of the current inputs and latch state. -/
  resetVal : (Fin nI → Bool) → (Fin nL → Bool) → Fin nL → Bool
  /-- per-latch next-state function of `(inputs, current state)`. -/
  next : (Fin nI → Bool) → (Fin nL → Bool) → Fin nL → Bool
  /-- good-states predicate `P` (no bad signal is set). -/
  good : (Fin nI → Bool) → (Fin nL → Bool) → Bool
  /-- AIGER 1.9 constraint predicate `C` (all constraints hold). -/
  cons : (Fin nI → Bool) → (Fin nL → Bool) → Bool

/-- A state assigns a Boolean to every latch. -/
abbrev State (M : SeqCircuit) := Fin M.nL → Bool
/-- An input valuation assigns a Boolean to every input. -/
abbrev Input (M : SeqCircuit) := Fin M.nI → Bool

/-- Reset predicate `R`: under input `ι`, every latch carries its reset value. -/
def R (M : SeqCircuit) (ι : Input M) (s : State M) : Prop :=
  ∀ l, s l = M.resetVal ι s l

/-- Two-state transition predicate `F`: every post-latch equals its next-state
    function evaluated on the pre-configuration. -/
def F (M : SeqCircuit) (ι : Input M) (s s' : State M) : Prop :=
  ∀ l, s' l = M.next ι s l

/-- Property evaluated at a configuration. -/
def evalP (M : SeqCircuit) (ι : Input M) (s : State M) : Bool := M.good ι s

/-- Constraint evaluated at a configuration. -/
def evalC (M : SeqCircuit) (ι : Input M) (s : State M) : Bool := M.cons ι s

/-- A **constrained run** of length `n`: a state/input sequence that starts in a reset
    state (under the first input), respects the transition relation, and satisfies the
    constraint at every visited configuration. -/
structure ConstrainedRun (M : SeqCircuit) (n : Nat) where
  st : Nat → State M
  inp : Nat → Input M
  reset0 : R M (inp 0) (st 0)
  cons_ok : ∀ i, i ≤ n → evalC M (inp i) (st i) = true
  trans_ok : ∀ i, i < n → F M (inp i) (st i) (st (i + 1))

/-- **Safety**: every constrained run, of every length, ends in a good state. -/
def Safe (M : SeqCircuit) : Prop :=
  ∀ n (τ : ConstrainedRun M n), evalP M (τ.inp n) (τ.st n) = true

/-- A **bad trace** of length `n`: a constrained run whose final configuration
    falsifies `P`. The length-indexed contrapositive of `Safe`. -/
def BadTrace (M : SeqCircuit) (n : Nat) : Prop :=
  ∃ τ : ConstrainedRun M n, evalP M (τ.inp n) (τ.st n) = false

/-- Safety is exactly the absence of bad traces of every length. -/
theorem safe_iff_no_bad (M : SeqCircuit) :
    Safe M ↔ ∀ n, ¬ BadTrace M n := by
  constructor
  · intro hs n hbad
    obtain ⟨τ, hb⟩ := hbad
    have ht := hs n τ
    rw [ht] at hb
    exact Bool.noConfusion hb
  · intro h n τ
    cases hp : evalP M (τ.inp n) (τ.st n) with
    | true => rfl
    | false => exact absurd ⟨τ, hp⟩ (h n)

end KernelCert
