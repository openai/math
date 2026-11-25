import OAI.Computability.FourierCircuit.Triangular
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! # Borrowed registers for triangular Toeplitz multiplication

The coefficient recursion implements the diagonal commutator. A product of
three additive shears and one signed interchange implements a simultaneous
Toeplitz map and inverse on two occupied arrays.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Ring
variable {K : Type*} [CommRing K]

private def scalingCoeff (u : K) (h : PowerSeries K) (i : ℕ) : K :=
  if i = 0 then 1 else
    (∑ j : Fin i, scalingCoeff u h j.val * PowerSeries.coeff (i-j.val) h) * (u^i-1)⁻¹ʳ
termination_by i
decreasing_by exact j.isLt

/-- The truncated equation f(uX)=h(X)f(X), solved coefficient by coefficient. -/
theorem exists_scaling_series_of_units {a : ℕ} {u : K}
    (hu : ∀ i, 0 < i → i < a → IsUnit (u ^ i - 1))
    (h : PowerSeries K) (hh : h.constantCoeff = 1) :
    ∃ f : PowerSeries K, f.constantCoeff = 1 ∧
      ∀ i < a, u^i * PowerSeries.coeff i f = PowerSeries.coeff i (h*f) := by
  let f := PowerSeries.mk (scalingCoeff u h)
  have hf0 : f.constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [f, scalingCoeff]
  refine ⟨f,hf0,?_⟩
  intro i hi
  rcases eq_or_ne i 0 with rfl | hne
  · simp [hf0, hh]
  have hunit := hu i (Nat.pos_of_ne_zero hne) hi
  rw [mul_comm h f, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, hh, mul_one,
    f, PowerSeries.coeff_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  have hs : scalingCoeff u h i =
      (∑ j : Fin i, scalingCoeff u h j.val * PowerSeries.coeff (i-j.val) h) * (u^i-1)⁻¹ʳ := by
    rw [scalingCoeff, ite_eq_right hne]
  have hc := congrArg (· * (u^i-1)) hs
  rw [Ring.inverse_mul_cancel_right _ _ hunit] at hc
  linear_combination hc

/-- In a field each nontrivial power of a primitive root differs from one by a unit. -/
theorem exists_scaling_series {F : Type*} [Field F] {a b : ℕ} (hab : a ≤ b)
    {u : F} (hu : IsPrimitiveRoot u b) (h : PowerSeries F) (hh : h.constantCoeff = 1) :
    ∃ f : PowerSeries F, f.constantCoeff = 1 ∧
      ∀ i < a, u^i * PowerSeries.coeff i f = PowerSeries.coeff i (h*f) :=
  exists_scaling_series_of_units
    (fun _ hi hi' => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr
      (hu.pow_ne_one_of_pos_of_lt hi.ne' (hi'.trans_le hab)))) h hh

open ExactFourier.CoefficientTime

/-- The diagonal basis change induced by scaling the series variable by `u`. -/
def scalingDiagonal (a : ℕ) (u : K) : Matrix (Fin a) (Fin a) K :=
  Matrix.diagonal fun i ↦ u ^ i.val

theorem scalingDiagonal_mul_inv {K : Type*} [Field K] (a : ℕ) {u : K} (hu : u ≠ 0) :
    scalingDiagonal a u * scalingDiagonal a u⁻¹ = 1 := by
  rw [scalingDiagonal, scalingDiagonal, Matrix.diagonal_mul_diagonal]
  simp [hu, ← Matrix.diagonal_one]

/-- Unit differences of powers give a commutator expression without division
outside the coefficient ring. The two Toeplitz factors are mutual inverses. -/
theorem toeplitz_commutator_units {a : ℕ} (u : Kˣ)
    (hu : ∀ i, 0 < i → i < a → IsUnit ((u : K)^i - 1))
    (h : PowerSeries K) (hh : h.constantCoeff = 1) :
    ∃ f : (PowerSeries K)ˣ, truncMatrix a h =
      scalingDiagonal a (u : K) * truncMatrix a (f : PowerSeries K) *
        scalingDiagonal a (↑u⁻¹ : K) * truncMatrix a (↑f⁻¹ : PowerSeries K) := by
  obtain ⟨f, hf, he⟩ := exists_scaling_series_of_units hu h hh
  obtain ⟨F, hF⟩ : IsUnit f := PowerSeries.isUnit_iff_constantCoeff.mpr (hf ▸ isUnit_one)
  subst f
  refine ⟨F, ?_⟩
  have hDS : scalingDiagonal a (u : K) * truncMatrix a (F : PowerSeries K) =
      truncMatrix a (h*(F : PowerSeries K)) * scalingDiagonal a (u : K) := by
    ext i j
    simp only [scalingDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, truncMatrix]
    split_ifs with hij
    · rw [← he (i.val-j.val) (lt_of_le_of_lt (Nat.sub_le _ _) i.isLt)]
      rw [show (u : K) ^ i.val = u ^ (i.val - j.val) * u ^ j.val by rw [← pow_add, Nat.sub_add_cancel hij]]
      ring
    · simp
  have hinv : scalingDiagonal a (u : K) * scalingDiagonal a (↑u⁻¹ : K) = 1 := by
    rw [scalingDiagonal, scalingDiagonal, Matrix.diagonal_mul_diagonal]
    simp [← mul_pow, ← Matrix.diagonal_one]
  rw [hDS, Matrix.mul_assoc (truncMatrix a _), hinv, Matrix.mul_one, ← truncMatrix_mul,
    mul_assoc, Units.mul_inv, mul_one]

/-- The matrix commutator for a lower triangular Toeplitz factor of main diagonal one.
Both the conjugating Toeplitz map and its inverse come from truncated series. -/
theorem toeplitz_commutator {K : Type*} [Field K] {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    {u : K} (hu : IsPrimitiveRoot u b) (h : PowerSeries K) (hh : h.constantCoeff = 1) :
    ∃ f : PowerSeries K, f.constantCoeff = 1 ∧
      truncMatrix a h = scalingDiagonal a u * truncMatrix a f *
        scalingDiagonal a u⁻¹ * truncMatrix a f⁻¹ := by
  obtain ⟨f, hf, he⟩ := exists_scaling_series hab hu h hh
  refine ⟨f,hf,?_⟩
  have hDS : scalingDiagonal a u * truncMatrix a f =
      truncMatrix a (h*f) * scalingDiagonal a u := by
    ext i j
    simp only [scalingDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, truncMatrix]
    split_ifs with hij
    · rw [← he (i.val-j.val) (lt_of_le_of_lt (Nat.sub_le _ _) i.isLt)]
      rw [show u ^ i.val = u ^ (i.val - j.val) * u ^ j.val by rw [← pow_add, Nat.sub_add_cancel hij]]
      ring
    · simp
  rw [hDS, Matrix.mul_assoc (truncMatrix a (h*f)), scalingDiagonal_mul_inv a
    (hu.ne_zero (ha.trans_le hab).ne'), Matrix.mul_one, ← truncMatrix_mul,
    mul_assoc, PowerSeries.mul_inv_cancel f (hf.trans_ne one_ne_zero), mul_one]

/-- On two occupied arrays, three additive updates and a signed interchange
implement a simultaneous map and inverse. -/
theorem paired_toeplitz_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Matrix ι ι K) (hST : S * T = 1) (hTS : T * S = 1) :
    Matrix.fromBlocks 1 S 0 1 * Matrix.fromBlocks 1 0 (-T) 1 *
        Matrix.fromBlocks 1 S 0 1 * Matrix.fromBlocks 0 (-1) 1 0 =
      Matrix.fromBlocks S 0 0 T := by
  simp [Matrix.fromBlocks_multiply, hST, hTS]

/-- Conjugating the paired maps acts on the first array and restores the second,
including when the second array starts with arbitrary contents. -/
theorem paired_commutator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D D' S T : Matrix ι ι K) (hTS : T * S = 1) :
    Matrix.fromBlocks D 0 0 (1 : Matrix ι ι K) * Matrix.fromBlocks S 0 0 T *
        Matrix.fromBlocks D' 0 0 1 * Matrix.fromBlocks T 0 0 S =
      Matrix.fromBlocks (D * S * D' * T) 0 0 1 := by
  simp [Matrix.fromBlocks_multiply, hTS]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
