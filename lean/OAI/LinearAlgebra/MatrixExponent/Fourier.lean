import OAI.LinearAlgebra.MatrixExponent.Coefficients
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Characteristic-independent Fourier separation

Only phases of absolute value below `3 * M` occur. Either `5 * M` or
`5 * M - 1` is invertible in the coefficient field. Use a primitive root
of that order and pad the average with zero to keep exactly `5 * M` copies.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Fourier

theorem exists_weights {M : ℕ} (hM : 0 < M) :
    ∃ (ζ : Coeff) (w : Fin (5 * M) → Coeff), ζ ≠ 0 ∧
      ∀ e : ℤ, -(3 * (M : ℤ)) < e → e < 3 * (M : ℤ) →
        (∑ r : Fin (5 * M), w r * ζ ^ ((r : ℤ) * e)) = if e = 0 then 1 else 0 := by
  obtain ⟨L, hlow, hhigh, hL⟩ :
      ∃ L : ℕ, 3 * M ≤ L ∧ L ≤ 5 * M ∧ (L : Coeff) ≠ 0 := by
    by_cases h : ((5 * M : ℕ) : Coeff) = 0
    · refine ⟨5 * M - 1, by omega, by omega, ?_⟩
      rw [Nat.cast_sub (by omega), h, Nat.cast_one, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
    · exact ⟨5 * M, by omega, le_rfl, h⟩
  have : NeZero (L : Coeff) := ⟨hL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Coeff L
  let w (r : ℕ) : Coeff := if r < L then (L : Coeff)⁻¹ else 0
  refine ⟨ζ, fun r => w r, hζ.ne_zero (by omega), ?_⟩
  intro e he he'
  have hs : (∑ r : Fin (5 * M), w r * ζ ^ ((r : ℤ) * e)) =
      (L : Coeff)⁻¹ * ∑ r ∈ Finset.range L, (ζ ^ e) ^ r := by
    simp_rw [zpow_mul', zpow_natCast]
    rw [← Finset.sum_range (fun r => w r * (ζ ^ e) ^ r), Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.range_mono hhigh) (by
      intro r _ hr
      simp [w, Finset.mem_range.not.mp hr])]
    apply Finset.sum_congr rfl
    intro r hr
    simp [w, Finset.mem_range.mp hr]
  rw [hs]
  by_cases he0 : e = 0
  · simp [he0, hL]
  · have hne : ζ ^ e ≠ 1 := by
      intro h
      exact he0 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ((hζ.zpow_eq_one_iff_dvd e).mp h)
        (by omega))
    have hperiod : (ζ ^ e) ^ L = 1 := by
      rw [← zpow_natCast, ← zpow_mul, hζ.zpow_eq_one_iff_dvd]
      exact dvd_mul_left _ _
    rw [geom_sum_eq hne, hperiod]
    simp [he0]

end OAI.LinearAlgebra.MatrixExponent.Fourier
