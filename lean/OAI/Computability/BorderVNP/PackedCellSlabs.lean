import OAI.Computability.BorderVNP.PackedCells

/-! # Compact bit intervals in sparse public row order

The used rows of a cell may have arbitrary public IDs and widths, including zero.
The consecutive intervals in increasing ID order fill a vector of exactly the
sum of their widths. This makes guessing that vector equivalent to guessing
each live wire once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellSlabs

open scoped Classical BigOperators

variable {A : Type*} [Fintype A] (row : A ↪ ℕ) (width : A → ℕ)

/-- Bit address at which a row starts in its owning cell's slab. -/
noncomputable def start (a : A) : ℕ := ∑ t, if row t < row a then width t else 0

private theorem end_eq (a : A) :
    start row width a + width a = ∑ t, if row t ≤ row a then width t else 0 := by
  rw [start, ← show (∑ t : A, if t = a then width t else 0) = width a by simp, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : t = a
  · subst t
    simp
  · have hn := row.injective.ne h
    rcases lt_or_gt_of_ne hn with hlt | hgt <;> simp [*,lt_asymm,le_of_lt,not_le_of_gt]

/-- The closed upper endpoint of every row fits, even when the row is empty. -/
theorem end_le_capacity (a : A) : start row width a + width a ≤ ∑ t, width t := by
  rw [end_eq]
  exact Finset.sum_le_sum fun t _ => by split <;> simp

private theorem end_le_start {a b : A} (h : row a < row b) :
    start row width a + width a ≤ start row width b := by
  rw [end_eq, start]
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : row t ≤ row a
  · simp [ht,ht.trans_lt h]
  · simp [ht]

/-- Row-major interval packing is bijective on all and only the live bits. -/
noncomputable def ordinal : (Σ a, Fin (width a)) ≃ Fin (∑ t, width t) :=
  let f (x : Σ a, Fin (width a)) : Fin (∑ t, width t) :=
    ⟨start row width x.1 + x.2.val,
      (Nat.add_lt_add_left x.2.isLt _).trans_le (end_le_capacity row width x.1)⟩
  Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨by
    rintro ⟨a,i⟩ ⟨b,j⟩ eqn
    have he : start row width a + i.val = start row width b + j.val := congrArg Fin.val eqn
    rcases lt_trichotomy (row a) (row b) with h | h | h
    · have := end_le_start row width h
      have := i.isLt
      omega
    · obtain rfl := row.injective h
      obtain rfl := Fin.ext (Nat.add_left_cancel he)
      rfl
    · have := end_le_start row width h
      have := j.isLt
      omega, by simp⟩)

/-- Packed addresses retain the lane order within every cable or site. -/
theorem ordinal_val (a : A) (i : Fin (width a)) :
    (ordinal row width ⟨a,i⟩).val = start row width a + i.val := rfl

/-- Read a compact vector as the tuple of words stored in its physical rows. -/
noncomputable def words : (Fin (∑ t, width t) → Bool) ≃ (∀ t, Fin (width t) → Bool) :=
  ((Equiv.arrowCongr (ordinal row width).symm (Equiv.refl Bool)).trans (Equiv.piCurry (fun _ _ => Bool)))

/-- Reads use precisely the publicly determined base and the lane ordinal. -/
theorem words_apply (x : Fin (∑ t, width t) → Bool) (a : A) (i : Fin (width a)) :
    words row width x a i = x (ordinal row width ⟨a,i⟩) := rfl

end Packing.CellSlabs

end BorderVNP
end Computability
end OAI
