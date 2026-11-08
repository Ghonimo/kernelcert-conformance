import KernelCert.Enum
open KernelCert

-- the enumeration has 2^n entries and contains every valuation
example : (allFns 3).length = 8 := by decide
example (g : Fin 4 → Bool) : g ∈ allFns 4 := mem_allFns 4 g
-- quantifiers over valuations decide by evaluation, with the right answers
#guard decide (∀ f : Fin 3 → Bool, (f 0 && f 1) = (f 1 && f 0))
#guard !(decide (∀ f : Fin 2 → Bool, f 0 = true))
#guard decide (∃ f : Fin 2 → Bool, f 0 = true ∧ f 1 = false)
#guard !(decide (∃ f : Fin 2 → Bool, f 0 = true ∧ f 0 = false))
-- flipping one coordinate
#guard flipAt (fun i : Fin 3 => decide (i.val = 0)) 1 1 = true
#guard flipAt (fun i : Fin 3 => decide (i.val = 0)) 1 0 = true
-- the single-flip criterion: a function invariant under flips outside A depends only on A
example (f : (Fin 3 → Bool) → Bool) (hf : ∀ s b, b.val ≠ 0 → f (flipAt s b) = f s)
    (s s' : Fin 3 → Bool) (h0 : s 0 = s' 0) : f s = f s' :=
  dep_of_flips f (fun b => b.val = 0) (fun s b hb => hf s b hb) s s'
    (fun b hb => by have : b = 0 := Fin.ext hb; rw [this]; exact h0)
