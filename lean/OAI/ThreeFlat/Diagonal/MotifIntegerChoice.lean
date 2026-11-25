import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Integer selection of a demand tile

All demand tiles are fixed before the widths are known. Choose the tile
which needs the fewest copies and break ties by its fixed table order.
The overflow value is one past the sum of the demand widths, so every
viable tile has a smaller score, even when some coordinates vanish.
-/

namespace ThreeFlat.Diagonal.MotifIntegerChoice

open scoped BigOperators

/-- Required copies for one coordinate. `bad` denotes an absent positive-width demand. -/
def need (bad b d : ℕ) : ℕ :=
  if d = 0 then if b = 0 then 0 else bad else (b + d - 1) / d

theorem need_le_iff {bad b d m : ℕ} (good : m < bad) : need bad b d ≤ m ↔ b ≤ d*m := by
  by_cases hd : d = 0
  · subst d; by_cases hb : b = 0 <;> simp [need,hb, Nat.not_le.mpr good]
  · simpa only [need, ite_eq_right hd, ← Nat.ceilDiv_eq_add_pred_div] using
      (ceilDiv_le_iff_le_mul (b := b) (c := m) (Nat.pos_of_ne_zero hd))

/-- Fixed-order minimization. Later entries win only on strict improvement. -/
def best {T : Type*} (value : T → ℕ) : T → List T → T
  | z, [] => z
  | z, i :: l => best value (if value i < value z then i else z) l

theorem best_le {T : Type*} (v : T → ℕ) (z : T) (l : List T) :
    ∀ i ∈ z::l, v (best v z l) ≤ v i := by
  induction l generalizing z with
  | nil => simp [best]
  | cons j l ih =>
    intro i hi
    simp only [List.mem_cons] at hi
    by_cases h : v j < v z
    · rw [best, ite_eq_left h]
      rcases hi with rfl | rfl | hil
      · exact (ih j j (by simp)).trans h.le
      · exact ih _ _ (by simp)
      · exact ih _ _ (by simp [hil])
    · rw [best, ite_eq_right h]
      rcases hi with rfl | rfl | hil
      · exact ih _ _ (by simp)
      · exact (ih z z (by simp)).trans (le_of_not_gt h)
      · exact ih _ _ (by simp [hil])

variable {E T : Type*} [Fintype E] [DecidableEq E]

def sentinel (b : E → ℕ) := 1 + ∑ e, b e

def score (b : E → ℕ) (d : T → E → ℕ) (i : T) := Finset.univ.sup (fun e => need (sentinel b) (b e) (d i e))

omit [DecidableEq E] in
theorem score_le {b : E → ℕ} {d : T → E → ℕ} {i : T} {m : ℕ} (hm : m < sentinel b) :
    score b d i ≤ m ↔ ∀ e, b e ≤ d i e * m := by
  simp only [score, Finset.sup_le_iff, Finset.mem_univ, true_implies, need_le_iff hm]

omit [DecidableEq E] in
/-- An arbitrary witness from the spectral grid yields an integer-selected
viable tile using at most as many copies as the witness. -/
theorem best_grid (b : E → ℕ) (d : T → E → ℕ) (first : T) (rows : List T)
    (tile : T) (ht : tile ∈ first::rows) (r : ℕ) (fits : ∀ e, b e ≤ d tile e * r) :
    let i := best (score b d) first rows
    score b d i ≤ r ∧ ∀ e, b e ≤ d i e * score b d i := by
  let m := min r (∑ e, b e)
  have hm : m < sentinel b := by dsimp [m,sentinel]; omega
  have hgrid : score b d tile ≤ m := (score_le hm).mpr fun e => by
    by_cases zero : d tile e = 0
    · simpa only [zero, zero_mul] using fits e
    · have h : b e ≤ ∑ j, b j := Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      dsimp only [m]
      rcases le_total r (∑ j, b j) with hle | hge
      · simpa only [min_eq_left hle] using fits e
      · rw [min_eq_right hge]
        exact h.trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero zero))
  have bound := (best_le (score b d) first rows tile ht).trans hgrid
  exact ⟨bound.trans (min_le_left ..), (score_le (lt_of_le_of_lt bound hm)).mp le_rfl⟩

end ThreeFlat.Diagonal.MotifIntegerChoice

end OAI
