import Mathlib.Data.Nat.BitIndices

namespace OAI
/-! # Least-set-bit lookup contents -/

namespace Hierarchy.ProbeStage.MaskWords

/-- The shared `2^b`-entry lookup table holds this least set position. -/
def least (x : ℕ) := x.bitIndices.headD 0

theorem least_spec {x : ℕ} (hx : x ≠ 0) : x.testBit (least x) = true ∧
    ∀ i, x.testBit i = true → least x ≤ i := by
  have hne : x.bitIndices ≠ [] := by
    intro h
    have hsum := Nat.sum_map_two_pow_bitIndices x
    rw [h] at hsum
    exact hx (by simpa using hsum.symm)
  cases he : x.bitIndices with
  | nil => exact False.elim (hne he)
  | cons a l =>
    have sorted := @Nat.bitIndices_sorted x
    rw [he] at sorted
    have hlt := List.pairwise_cons.mp sorted.pairwise
    simp only [least,he,List.headD_cons]
    constructor
    · exact Nat.mem_bitIndices.mp (by rw [he]; simp)
    · intro i hi
      have hh := Nat.mem_bitIndices.mpr hi
      rw [he,List.mem_cons] at hh
      exact hh.elim (fun h => h.ge) (fun h => (hlt.1 _ h).le)

end Hierarchy.ProbeStage.MaskWords

end OAI
