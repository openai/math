import OAI.Computability.BorderVNP.CubeISAHeaderDecode

/-! # Individual words returned by the native declaration decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.HeaderDecode

open Cube.SelectorRead Finset

/-- A visited dense entry is exactly its decoded upper value or lower zero. -/
theorem Layout.imageEntry (l : Layout) (old : ℕ → ℕ) {k : ℕ} (hk : k < l.entries) :
    l.image old l.entries (l.dense+k) = l.value old k := by
  simp [Layout.image,hk]

/-- The compact decoder stores the precise coordinate word at the secondary
header's fifth offset. -/
theorem Layout.finalCoordinate (l : Layout) (old : ℕ → ℕ)
    (dense : l.header+5 < l.dense ∨ l.dense+l.entries ≤ l.header+5)
    (totals : l.header+5 < l.totals ∨ l.totals+l.a ≤ l.header+5) :
    l.finalImage old (l.header+5) = (decoded old l.source l.cw).val := by
  simp only [Layout.finalImage,HeaderTotals.image,Layout.image,
    ite_eq_right (show ¬(l.totals ≤ l.header+5 ∧ l.header+5 < l.totals+l.a) by omega),
    ite_eq_right (show ¬(l.dense ≤ l.header+5 ∧ l.header+5 < l.dense+l.entries) by omega),ite_true]

/-- The subsequent column pass preserves each decoded dense word. -/
theorem Layout.finalEntry (l : Layout) (old : ℕ → ℕ) {k : ℕ} (hk : k < l.entries)
    (separate : l.dense+l.entries ≤ l.totals ∨ l.totals+l.a ≤ l.dense) :
    l.finalImage old (l.dense+k) = l.value old k := by
  simp only [Layout.finalImage,HeaderTotals.image,
    ite_eq_right (show ¬(l.totals ≤ l.dense+k ∧ l.dense+k < l.totals+l.a) by omega),l.imageEntry old hk]

/-- Each public total is the exact natural sum of the dense decoded values in its column. -/
theorem Layout.finalTotal (l : Layout) (old : ℕ → ℕ) {j : ℕ} (hj : j < l.a) :
    l.finalImage old (l.totals+j) = ∑ k ∈ range (l.d*l.d), l.value old (k*l.a+j) := by
  simp only [Layout.finalImage,HeaderTotals.image,ite_eq_left (show l.totals ≤ l.totals+j ∧ l.totals+j < l.totals+l.a by omega),
    Nat.add_sub_cancel_left,HeaderTotals.sumAt]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  rw [Nat.add_assoc]
  apply l.imageEntry
  calc k*l.a+j < (k+1)*l.a := by rw [Nat.add_mul]; omega
       _ ≤ _ := Nat.mul_le_mul_right l.a hk

/-- Every word outside the coordinate cell, dense claimed rows, and totals is
preserved, including the actual-row table in a disjoint allocation. -/
theorem Layout.finalOutside (l : Layout) (old : ℕ → ℕ) {x : ℕ} (coordinate : x ≠ l.header+5)
    (dense : x < l.dense ∨ l.dense+l.entries ≤ x) (totals : x < l.totals ∨ l.totals+l.a ≤ x) :
    l.finalImage old x = old x := by
  simp only [Layout.finalImage,HeaderTotals.image,Layout.image,
    ite_eq_right (show ¬(l.totals ≤ x ∧ x < l.totals+l.a) by omega),
    ite_eq_right (show ¬(l.dense ≤ x ∧ x < l.dense+l.entries) by omega),ite_eq_right coordinate]

end RoutingISA.HeaderDecode

end BorderVNP
end Computability
end OAI
