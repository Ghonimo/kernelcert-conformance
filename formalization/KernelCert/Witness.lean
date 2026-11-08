/-
  KernelCert.Witness: witness circuits, the shared interface (latches and inputs), and
  the five checks as obligations on runs.

  * Reset: every constrained reset of `M` is matched, on the shared latches, by SOME
    reset of `W` that satisfies `C'`.
  * Transition: every constrained step of `M`, from a `W`-state that agrees on the shared
    latches and satisfies `C'`, is matched by SOME `W`-successor.
  * Property, Base, Step: `P'` implies `P` on agreeing configurations; `P'` holds at every
    reset of `W` and is preserved by its steps.
  Shared inputs are identified by `AgreeIn`. Reset and Transition are existential in the
  witness state: a universal conclusion fails for a witness whose `R'` and `F'` pin a
  latch outside `K` that the agreement leaves free (Counterexamples.lean refutes both
  forms for one such witness). Level2.lean derives these obligations from the combinational
  checks Certifaiger runs.
-/
import KernelCert.Circuit

namespace KernelCert
variable {M : SeqCircuit}

/-- A witness circuit for `M`, with the shared interface supplied as data:
    `k` shared latches (`K = L ∩ L'`) and `kIn` shared inputs, each given by a pair of
    injections into `M`'s and `W`'s index spaces. Materialising these from the AIGER
    `=`/`MAPPING` symbol table is the job of the (trusted) front-end; the metatheorem
    is proved for whatever embeddings it supplies. -/
structure Witness (M : SeqCircuit) where
  W : SeqCircuit
  k : Nat
  embM : Fin k → Fin M.nL
  embW : Fin k → Fin W.nL
  embM_inj : ∀ a b : Fin k, embM a = embM b → a = b
  embW_inj : ∀ a b : Fin k, embW a = embW b → a = b
  kIn : Nat
  inM : Fin kIn → Fin M.nI
  inW : Fin kIn → Fin W.nI
  inM_inj : ∀ a b : Fin kIn, inM a = inM b → a = b
  inW_inj : ∀ a b : Fin kIn, inW a = inW b → a = b

/-- Two states **agree on `K`** when they carry the same values on the shared latches. -/
def Agree (κ : Witness M) (sM : State M) (sW : State κ.W) : Prop :=
  ∀ j : Fin κ.k, sM (κ.embM j) = sW (κ.embW j)

/-- Two input valuations **agree on the shared inputs** (the input half of the
    `=`/`MAPPING` convention). -/
def AgreeIn (κ : Witness M) (ιM : Input M) (ιW : Input κ.W) : Prop :=
  ∀ j : Fin κ.kIn, ιM (κ.inM j) = ιW (κ.inW j)

/-- (1) **Reset (semantic form).** Every constrained reset of `M` is matched, on `K`,
    by SOME full reset of `W` satisfying `W`'s constraint — the conclusion the
    K-restricted combinational reset check plus the stratification-backed
    reset-extension lemma (CAV'25 Lemma 1) will justify at Level 2. -/
def ResetCheck (κ : Witness M) : Prop :=
  ∀ (ιM : Input M) (ιW : Input κ.W) (sM : State M),
    AgreeIn κ ιM ιW → R M ιM sM → evalC M ιM sM = true →
    ∃ sW : State κ.W, Agree κ sM sW ∧ R κ.W ιW sW ∧ evalC κ.W ιW sW = true

/-- (2) **Transition (semantic form).** A constrained step of `M` (per-frame inputs,
    per-frame constraints), from any `W`-state that K-agrees with the pre-state and
    satisfies `C'`, is matched by SOME `W`-successor that K-agrees with the post-state
    and re-establishes `C'` — the conclusion functionality of `F'` delivers (evaluate
    `W`'s next-state functions on the full pre-state; the combinational check certifies
    its K-projection and constraint preservation). -/
def TransitionCheck (κ : Witness M) : Prop :=
  ∀ (ι0 ι1 : Input M) (ιW0 ιW1 : Input κ.W)
    (s0 s1 : State M) (s0' : State κ.W),
    AgreeIn κ ι0 ιW0 → AgreeIn κ ι1 ιW1 → Agree κ s0 s0' →
    F M ι0 s0 s1 → evalC M ι0 s0 = true → evalC M ι1 s1 = true →
    evalC κ.W ιW0 s0' = true →
    ∃ s1' : State κ.W, Agree κ s1 s1' ∧ F κ.W ιW0 s0' s1' ∧ evalC κ.W ιW1 s1' = true

/-- (3) **Property.** Where both constraints hold, on interface-agreeing
    configurations, `W` being good forces `M` to be good (`P' ⇒ P`). -/
def PropertyCheck (κ : Witness M) : Prop :=
  ∀ (ιM : Input M) (ιW : Input κ.W) (sM : State M) (sW : State κ.W),
    AgreeIn κ ιM ιW → Agree κ sM sW →
    evalC M ιM sM = true → evalC κ.W ιW sW = true →
    (evalP κ.W ιW sW = true → evalP M ιM sM = true)

/-- (4) **Base (initiation).** Every reset state of `W`, under its constraint, is good. -/
def BaseCheck (κ : Witness M) : Prop :=
  ∀ (ιW : Input κ.W) (sW : State κ.W),
    R κ.W ιW sW → evalC κ.W ιW sW = true → evalP κ.W ιW sW = true

/-- (5) **Step (consecution).** If `W` is good and takes a constrained step (per-frame
    inputs and constraints), it is good in the post-frame. Together with (4) this makes
    `P'` a 1-inductive invariant of `W`. -/
def StepCheck (κ : Witness M) : Prop :=
  ∀ (ι0 ι1 : Input κ.W) (s0' s1' : State κ.W),
    evalP κ.W ι0 s0' = true → F κ.W ι0 s0' s1' →
    evalC κ.W ι0 s0' = true → evalC κ.W ι1 s1' = true →
    evalP κ.W ι1 s1' = true

end KernelCert
