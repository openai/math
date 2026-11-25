import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Vandermonde checks for bounded-column repair -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Matrix

variable {R : Type*} [CommRing R] {W s j : ℕ}

/-- The parity-check matrix on the nodes `ρ`, using exponents from zero to `s - 1`. -/
def repairCheck (ρ : Fin W → R) (s : ℕ) : Matrix (Fin s) (Fin W) R :=
  fun t u => ρ u ^ t.val

/-- Any selection of at most `s` columns has a left inverse when differences
of distinct nodes are units. The first `j` checks already recover the `j` columns. -/
theorem repairCheck_leftInverse (ρ : Fin W → R)
    (hρ : Pairwise (fun u v => IsUnit (ρ u - ρ v))) (hjs : j ≤ s) (e : Fin j ↪ Fin W) :
    ∃ L : Matrix (Fin j) (Fin s) R, L * (repairCheck ρ s).submatrix id e = 1 := by
  let V := (Matrix.vandermonde (fun i => ρ (e i)))ᵀ
  let P : Matrix (Fin j) (Fin s) R := fun i t => if i.castLE hjs = t then 1 else 0
  have hV : IsUnit V.det := by
    rw [Matrix.det_transpose, Matrix.det_vandermonde, IsUnit.prod_univ_iff]
    intro i
    apply IsUnit.prod_iff.mpr
    intro k hk
    exact hρ (e.injective.ne (Finset.mem_Ioi.mp hk).ne')
  have hP : P * (repairCheck ρ s).submatrix id e = V := by
    ext i u
    rw [Matrix.mul_apply]
    simp [P, V, Matrix.submatrix, repairCheck, ite_mul, Matrix.vandermonde_apply]
  exact ⟨V⁻¹ * P, by rw [Matrix.mul_assoc, hP, Matrix.nonsing_inv_mul _ hV]⟩

end FiniteFourier
end LinearAlgebra
end OAI
