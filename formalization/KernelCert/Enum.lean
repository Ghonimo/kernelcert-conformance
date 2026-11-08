/-
  KernelCert.Enum — finite enumeration of Boolean valuations, so that the checks can be
  decided by evaluation, and the single-flip criterion for dependence.

  * `allFns n` lists every valuation `Fin n → Bool` (`mem_allFns`), which gives
    `Decidable` instances for `∀` and `∃` over valuations.
  * `dep_of_flips`: a function of a valuation that does not change when any single
    coordinate outside a set `A` is negated depends only on the coordinates in `A`.
    This turns "the reset value depends only on lower and shared latches" into a check
    over single flips, which is far cheaper to decide than one over pairs of states.
-/
namespace KernelCert

/-- All valuations `Fin n → Bool`. -/
def allFns : (n : Nat) → List (Fin n → Bool)
  | 0 => [fun i => i.elim0]
  | n + 1 => (allFns n).flatMap fun f =>
      [fun i => if h : i.val < n then f ⟨i.val, h⟩ else false,
       fun i => if h : i.val < n then f ⟨i.val, h⟩ else true]

/-- Every valuation is in the enumeration. -/
theorem mem_allFns : ∀ (n : Nat) (g : Fin n → Bool), g ∈ allFns n
  | 0, g => by
    have hg : g = fun i => i.elim0 := funext fun i => i.elim0
    rw [hg]
    exact List.mem_singleton.mpr rfl
  | n + 1, g => by
    let g' : Fin n → Bool := fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    have key : ∀ b : Bool, g ⟨n, Nat.lt_succ_self n⟩ = b →
        g = fun i => if h : i.val < n then g' ⟨i.val, h⟩ else b := by
      intro b hb
      funext i
      by_cases h : i.val < n
      · rw [dite_eq_left h]
      · rw [dite_eq_right h]
        have hi : i = ⟨n, Nat.lt_succ_self n⟩ :=
          Fin.ext (by show i.val = n; have := i.isLt; omega)
        rw [hi, hb]
    rw [allFns, List.mem_flatMap]
    refine ⟨g', mem_allFns n g', ?_⟩
    cases hb : g ⟨n, Nat.lt_succ_self n⟩ with
    | false => rw [key false hb]; exact List.mem_cons_self
    | true => rw [key true hb]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- `∀` over valuations, decided by evaluating every valuation. -/
instance decForallFn {n : Nat} (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    Decidable (∀ f : Fin n → Bool, P f) :=
  decidable_of_iff ((allFns n).all (fun f => decide (P f)) = true) (by
    rw [List.all_eq_true]
    exact ⟨fun h f => of_decide_eq_true (h f (mem_allFns n f)),
           fun h f _ => decide_eq_true (h f)⟩)

/-- `∃` over valuations, decided by evaluating every valuation. -/
instance decExistsFn {n : Nat} (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    Decidable (∃ f : Fin n → Bool, P f) :=
  decidable_of_iff ((allFns n).any (fun f => decide (P f)) = true) (by
    rw [List.any_eq_true]
    exact ⟨fun ⟨f, _, hf⟩ => ⟨f, of_decide_eq_true hf⟩,
           fun ⟨f, hf⟩ => ⟨f, mem_allFns n f, decide_eq_true hf⟩⟩)

/-- `s` with coordinate `b` negated. -/
def flipAt {n : Nat} (s : Fin n → Bool) (b : Fin n) : Fin n → Bool :=
  fun x => if x = b then !(s x) else s x

/-- Interpolation from `s` to `s'`: coordinates below `k` from `s'`, the rest from `s`. -/
def mixUpTo {n : Nat} (s s' : Fin n → Bool) (k : Nat) : Fin n → Bool :=
  fun x => if x.val < k then s' x else s x

/-- **Single-flip criterion.** If negating any single coordinate outside `A` never
    changes `f`, then `f` agrees on any two valuations that agree on `A`. The proof walks
    from `s` to `s'` one coordinate at a time. -/
theorem dep_of_flips {n : Nat} {α : Type} (f : (Fin n → Bool) → α) (A : Fin n → Prop)
    (h : ∀ s b, ¬ A b → f (flipAt s b) = f s) :
    ∀ s s', (∀ b, A b → s b = s' b) → f s = f s' := by
  intro s s' hA
  have step : ∀ k, f (mixUpTo s s' k) = f s := by
    intro k
    induction k with
    | zero =>
      have e : mixUpTo s s' 0 = s := funext fun x => by
        simp only [mixUpTo, Nat.not_lt_zero, ite_false]
      rw [e]
    | succ k ih =>
      by_cases hk : k < n
      · have hb : (⟨k, hk⟩ : Fin n).val = k := rfl
        by_cases hsb : s ⟨k, hk⟩ = s' ⟨k, hk⟩
        · have e : mixUpTo s s' (k + 1) = mixUpTo s s' k := by
            funext x
            simp only [mixUpTo]
            by_cases hx : x.val < k
            · have hx1 : x.val < k + 1 := by omega
              rw [ite_eq_left hx1, ite_eq_left hx]
            · by_cases hxk : x.val = k
              · have hx1 : x.val < k + 1 := by omega
                have hxe : x = ⟨k, hk⟩ := Fin.ext hxk
                rw [ite_eq_left hx1, ite_eq_right hx, hxe, hsb]
              · have hx1 : ¬ x.val < k + 1 := by omega
                rw [ite_eq_right hx1, ite_eq_right hx]
          rw [e]; exact ih
        · have hnA : ¬ A ⟨k, hk⟩ := fun hab => hsb (hA _ hab)
          have e : mixUpTo s s' (k + 1) = flipAt (mixUpTo s s' k) ⟨k, hk⟩ := by
            funext x
            simp only [mixUpTo, flipAt]
            by_cases hxe : x = ⟨k, hk⟩
            · have hxk : x.val = k := by rw [hxe]
              have hx1 : x.val < k + 1 := by omega
              have hx0 : ¬ x.val < k := by omega
              rw [ite_eq_left hx1, ite_eq_left hxe, ite_eq_right hx0, hxe]
              revert hsb
              cases s ⟨k, hk⟩ <;> cases s' ⟨k, hk⟩ <;> simp
            · have hxk : x.val ≠ k := fun hv => hxe (Fin.ext hv)
              rw [ite_eq_right hxe]
              by_cases hx : x.val < k
              · have hx1 : x.val < k + 1 := by omega
                rw [ite_eq_left hx1, ite_eq_left hx]
              · have hx1 : ¬ x.val < k + 1 := by omega
                rw [ite_eq_right hx1, ite_eq_right hx]
          rw [e, h _ _ hnA]; exact ih
      · have e : mixUpTo s s' (k + 1) = mixUpTo s s' k := by
          funext x
          simp only [mixUpTo]
          have h1 : x.val < k := by have := x.isLt; omega
          have h2 : x.val < k + 1 := by omega
          rw [ite_eq_left h1, ite_eq_left h2]
        rw [e]; exact ih
  have hend : mixUpTo s s' n = s' := funext fun x => by
    simp only [mixUpTo]
    rw [ite_eq_left x.isLt]
  calc f s = f (mixUpTo s s' n) := (step n).symm
    _ = f s' := by rw [hend]

end KernelCert
