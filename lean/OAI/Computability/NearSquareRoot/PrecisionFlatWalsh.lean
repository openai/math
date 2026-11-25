import OAI.Computability.NearSquareRoot.PrecisionFlatWalshInteger
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNormalize
import OAI.Computability.NearSquareRoot.PrecisionRecordArithmetic
import OAI.Computability.NearSquareRoot.PrecisionDiagonal
import OAI.Computability.NearSquareRoot.SynchronizedNorm

/-! # A rounded selected Walsh transform on packed record addresses

The exact integer butterflies accumulate signed component numerators. One
dyadic normalization at each output converts those numerators to the data
grid. Spectator addresses remain fixed throughout the integer butterflies.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication Matrix SynchronizedPadding

/-- Select any set of packed address bits and normalize its integer butterfly
result using the selected width. -/
def selectedWalshStep {k : ℕ} (bits : Finset (Fin k)) (x : Fin (2^k) → Record k) :
    Fin (2^k) → Record k :=
  fun j => flatWalshRecord k bits.card (FlatWalshInteger.transform bits (fun i => Grid.aspect (x i)) j)

private theorem selectedWalsh_meaning {k : ℕ} (bits : Finset (Fin k))
    (u : (BoxFin.flatWalsh bits)ᴴ * BoxFin.flatWalsh bits = 1) (x : Fin (2^k) → Record k)
    (j : Fin (2^k)) :
    (SynchronizedPair.w : ℂ)^bits.card *
        (Grid.toC (FlatWalshInteger.transform bits (fun i => Grid.aspect (x i)) j) /
          (2 : ℂ)^fractionBits k) =
      matrixIsometry (BoxFin.flatWalsh bits) u (recordArray x) j := by
  rw [← mul_div_assoc, FlatWalshInteger.normalized_transform]
  change ((BoxFin.flatWalsh bits *ᵥ (fun i => Grid.toC (Grid.aspect (x i)))) j) / _ =
    (BoxFin.flatWalsh bits *ᵥ (fun i => Grid.toC (Grid.aspect (x i)) / (2:ℂ)^fractionBits k)) j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]

/-- One rounded stage on the original address space. The number of selected
bits may range from zero to all `k` bits. -/
theorem selectedWalshStep_error {k : ℕ} (hk : 1 ≤ k) (bits : Finset (Fin k))
    (u : (BoxFin.flatWalsh bits)ᴴ * BoxFin.flatWalsh bits = 1) (x : Fin (2^k) → Record k)
    (hx : ‖recordArray x‖ ≤ (2:ℝ)^(13*k)) :
    ‖recordArray (selectedWalshStep bits x) -
      matrixIsometry (BoxFin.flatWalsh bits) u (recordArray x)‖ ≤ 1/(2:ℝ)^(50*k) := by
  let ideal := matrixIsometry (BoxFin.flatWalsh bits) u (recordArray x)
  have hm : bits.card ≤ k := by simpa using Finset.card_le_univ bits
  have entry (j : Fin (2^k)) :
      ‖value k (selectedWalshStep bits x j) - ideal j‖ ≤ 1/(2:ℝ)^(68*k) := by
    have hj : ‖ideal j‖ ≤ (2:ℝ)^(13*k) := (PiLp.norm_apply_le ideal j).trans (by simpa [ideal] using hx)
    rw [← selectedWalsh_meaning bits u x j] at hj ⊢
    exact flatWalshRecord_error _ hk hm hj
  apply (euclidean_norm_le_of_coordinates _ (by positivity) entry).trans
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  have hdim : Real.sqrt ((2:ℝ)^k) ≤ 2^k := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
    nlinarith [one_le_pow₀ (n := k) (show (1:ℝ) ≤ 2 by norm_num)]
  apply (mul_le_mul_of_nonneg_right hdim (by positivity)).trans
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

end FixedPoint

end NearSquareRoot
end Computability
end OAI
