import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Positivity and size of integer Gram determinants for the lattice reduction and rounding steps. -/

open scoped BigOperators RealInnerProductSpace
open Submodule Matrix WithLp

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

variable {k p : ℕ}

/-- Expanding the determinant uses `k!` products of `k` bounded entries. -/
theorem abs_det_le_factorial_pow (G : Matrix (Fin k) (Fin k) ℤ)
    {B : ℤ} (hG : ∀ i j, |G i j| ≤ B) : |G.det| ≤ k.factorial * B ^ k := by
  calc
    |G.det| ≤ ∑ σ : Equiv.Perm (Fin k), |(Equiv.Perm.sign σ : ℤ) * ∏ i, G (σ i) i| := by
      rw [Matrix.det_apply']
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), B ^ k := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, Equiv.Perm.sign_abs, one_mul, Finset.abs_prod]
      calc
        _ ≤ ∏ _i : Fin k, B :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hG (σ i) i)
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]

/-- Coefficient bound on the Gram determinant for an arbitrary integer matrix. -/
theorem gram_det_bound (A : Matrix (Fin k) (Fin p) ℤ) {D : ℕ}
    (ha : ∀ i j, (A i j).natAbs ≤ D) :
    (A * Aᵀ).det.natAbs ≤ k.factorial * (p * D ^ 2) ^ k := by
  have hentry (i j : Fin k) : |(A * Aᵀ) i j| ≤ (p : ℤ) * (D : ℤ) ^ 2 := by
    rw [Matrix.mul_apply]
    calc
      _ ≤ ∑ l, |A i l * Aᵀ l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin p, (D : ℤ)^2 := by
        apply Finset.sum_le_sum
        intro l _
        rw [Matrix.transpose_apply, abs_mul, Int.abs_eq_natAbs, Int.abs_eq_natAbs, pow_two]
        exact_mod_cast Nat.mul_le_mul (ha i l) (ha j l)
      _ = _ := by simp
  have hh := abs_det_le_factorial_pow (A * Aᵀ) hentry
  rw [Int.abs_eq_natAbs] at hh
  exact_mod_cast hh


/-- Every leading Gram determinant of an independent integral row family is positive,
including the determinant of the empty prefix. -/
theorem leading_gram_det_pos {n : ℕ} (A : Matrix (Fin p) (Fin n) ℤ)
    (hli : LinearIndependent ℝ (fun i => (toLp 2 (fun j => (A i j : ℝ)) : EuclideanSpace ℝ (Fin n))))
    (k : ℕ) (hk : k ≤ p) :
    0 < ((A * Aᵀ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  let f := Fin.castLE hk
  let g (i : Fin k) : EuclideanSpace ℝ (Fin n) := toLp 2 (fun j => (A (f i) j : ℝ))
  have hind : LinearIndependent ℝ g := hli.comp f (Fin.castLE_injective hk)
  have hpos := (Matrix.posDef_gram_of_linearIndependent hind).det_pos
  have hgram : Matrix.gram ℝ g = ((A * Aᵀ).submatrix f f).map (Int.castRingHom ℝ) := by
    ext i j
    simp [Matrix.gram, g, Matrix.mul_apply, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hcast : (((A * Aᵀ).submatrix f f).det : ℝ) =
      (((A * Aᵀ).submatrix f f).map (Int.castRingHom ℝ)).det :=
    (Int.castRingHom ℝ).map_det _
  rw [hgram, ← hcast] at hpos
  exact_mod_cast hpos


/-- Initial squared Euclidean row lengths are bounded directly in terms of the
input coordinate magnitudes. -/
theorem integerRow_norm_sq_bound {n D : ℕ} (z : Fin n → ℤ)
    (hz : ∀ i, (z i).natAbs ≤ D) :
    ‖(toLp 2 (fun i => (z i : ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ (n : ℝ) * (D : ℝ)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin n, (D : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(z i : ℝ)‖ ^ 2 ≤ _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [Real.norm_eq_abs]
      have hZ : |z i| ≤ (D : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hz i
      exact_mod_cast hZ
    _ = _ := by simp

end Lattice
end LinearProgramming
end Optimization
end OAI
