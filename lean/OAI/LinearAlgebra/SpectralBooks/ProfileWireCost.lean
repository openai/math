import OAI.LinearAlgebra.SpectralBooks.CrossingShortening

/-! # Cost of the grouped wires and selector cables of one profile -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Crossing

open scoped BigOperators
noncomputable section

/-- A block of `n` width-`b` strings carries exactly `n*b` bits. -/
def blockCable (n b : ℕ) : (Fin n → Fin b → Bool) ≃ (Fin (n*b) → Bool) :=
  (Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl _))

/-- The number of cables is fixed by the one-copy configuration. Data widths are multiples of
letter counts, and each center-to-endpoint selector cable carries `j*b` bits. -/
def profileWireCost {D A : ℕ} (count : Fin A → ℕ)
    (wires : (a : Fin A) → Fin (count a) → Wire (AxisSite D)) (π : Fin A → ℕ) (j b : ℕ) : ℝ :=
  (∑ a, ∑ u, ((π a * (wires a u).width : ℕ) : ℝ) *
    dist (axisPoint (wires a u).left) (axisPoint (wires a u).right)) +
  ∑ v : Fin D × Bool, ((j * b : ℕ) : ℝ) * dist (axisPoint none) (axisPoint (some v))

theorem profileWireCost_le {D A m j b : ℕ} {budget ν : ℝ} {count : Fin A → ℕ}
    {wires : (a : Fin A) → Fin (count a) → Wire (AxisSite D)} {π : Fin A → ℕ}
    (hπ : ∑ a, π a = j)
    (hcost : ∀ a, ∑ u, wireCost (fun p q ↦ dist (axisPoint p) (axisPoint q)) (wires a u) ≤ budget)
    (hsave : budget + 2 * D * b ≤ (1 - ν) * 2 * D * m) :
    profileWireCost count wires π j b ≤ (1 - ν) * 2 * D * m * j := by
  have hunit (v : Fin D × Bool) : dist (axisPoint none) (axisPoint (some v)) = 1 := by
    rcases v with ⟨i, e⟩
    cases e <;> simp [axisPoint]
  have hc (a : Fin A) :
      ∑ u, ((π a * (wires a u).width : ℕ) : ℝ) *
          dist (axisPoint (wires a u).left) (axisPoint (wires a u).right) ≤ (π a : ℝ) * budget := by
    simpa only [wireCost, Finset.mul_sum, Nat.cast_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (hcost a) (Nat.cast_nonneg (π a))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hc a)
  rw [← Finset.sum_mul, ← Nat.cast_sum, hπ] at hsum
  simp only [Nat.cast_mul] at hsum
  unfold profileWireCost
  simp only [hunit, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith [mul_le_mul_of_nonneg_right hsave (Nat.cast_nonneg j)]

end
end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
