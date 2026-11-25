import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Ordered single-chunk updates with persistent auxiliary memory

When all positions visited by a block are distinct, both endpoint values of
each visited chunk are already determined. The only intermediate indices
which must still be summed are the auxiliary words.
-/

namespace ThreeFlat.Diagonal

variable {I A S F : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype A] [DecidableEq A] [Semiring F]

/-- One block acts on a collection of external chunks and one auxiliary word. -/
noncomputable def orderedBlock (tick : I → S → S → Matrix A A F) (slots : List I) :
    Matrix ((I → S) × A) ((I → S) × A) F := by
  classical
  exact fun x y => if ∀ i ∉ slots, x.1 i = y.1 i then
    (slots.map fun i => tick i (x.1 i) (y.1 i)).prod x.2 y.2 else 0

private theorem block_cons (tick : I → S → S → Matrix A A F) (i : I) (l : List I) (hi : i ∉ l) :
    orderedBlock tick [i] * orderedBlock tick l = orderedBlock tick (i :: l) := by
  classical
  ext ⟨x, a⟩ ⟨y, b⟩
  let m : I → S := Function.update x i (y i)
  have first : ∀ j ∉ [i], x j = m j := by
    intro j hj
    simp only [List.mem_singleton] at hj
    simp [m, Function.update_of_ne hj]
  have only : ∀ z : I → S, z ≠ m → ∀ c : A,
      orderedBlock tick [i] (x, a) (z, c) * orderedBlock tick l (z, c) (y, b) = 0 := by
    intro z hz c
    by_cases h₁ : ∀ j ∉ [i], x j = z j
    · by_cases h₂ : ∀ j ∉ l, z j = y j
      · exact (hz (funext fun j => by
          by_cases hji : j = i
          · subst j; simpa [m] using h₂ i hi
          · simpa [m, Function.update_of_ne hji] using (h₁ j (by simpa using hji)).symm)).elim
      · simp only [orderedBlock, h₂, ite_false, mul_zero]
    · simp only [orderedBlock, h₁, ite_false, zero_mul]
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single m (fun z _ hz => Finset.sum_eq_zero fun c _ => only z hz c)
    (fun bad => (bad (Finset.mem_univ m)).elim)]
  by_cases h : ∀ j ∉ i :: l, x j = y j
  · have second : ∀ j ∉ l, m j = y j := by
      intro j hj
      by_cases hji : j = i
      · subst j; simp [m]
      · simpa [m, Function.update_of_ne hji] using h j (by simp [hji, hj])
    simp only [orderedBlock, ite_eq_left first, ite_eq_left second, ite_eq_left h,
      List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
    have map_tail : (l.map fun j => tick j (m j) (y j)) =
        l.map fun j => tick j (x j) (y j) := by
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := fun he => hi (he ▸ hj)
      simp only [m, Function.update_of_ne hji]
    rw [map_tail, Matrix.mul_apply]
    simp only [m, Function.update_self]
  · have second : ¬ ∀ j ∉ l, m j = y j := by
      intro he
      apply h
      intro j hj
      have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self)
      have hjl : j ∉ l := fun e => hj (List.mem_cons_of_mem _ e)
      simpa [m, Function.update_of_ne hji] using he j hjl
    simp only [orderedBlock, ite_eq_right second, ite_eq_right h, mul_zero, Finset.sum_const_zero]

/-- The entry formula of the full chronological product. -/
theorem ordered_ticks_eq (tick : I → S → S → Matrix A A F) (l : List I)
    (hl : l.Nodup) :
    (l.map fun i => orderedBlock tick [i]).prod = orderedBlock tick l := by
  classical
  induction l with
  | nil =>
    ext ⟨x,a⟩ ⟨y,b⟩
    by_cases h : x = y
    · subst y; simp [orderedBlock, Matrix.one_apply]
    · have hn : ¬∀ i, x i = y i := fun e => h (funext e)
      simp [orderedBlock, h, hn]
  | cons i l ih =>
    obtain ⟨hi, hrest⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.prod_cons, ih hrest, block_cons tick i l hi]

end ThreeFlat.Diagonal

end OAI
