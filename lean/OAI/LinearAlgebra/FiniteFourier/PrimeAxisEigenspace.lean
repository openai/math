import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Equiv

/-! # Shifting the prime-axis eigenspaces

In the two-orbit prime-axis construction, the unit `Y` has eigenvalue `u`.
Multiplication by its powers transports the invariant basis `1,U` to the
basis `Y^j,U*Y^j` in frequency `j`.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Module

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Multiplication by `Y^j` identifies the fixed submodule with the
`u^j`-eigenspace of the prime-axis automorphism. -/
def primeAxisEigenspaceEquiv (σ : A ≃ₐ[R] A) (u : Rˣ) (Y : Aˣ)
    (hY : σ (Y : A) = (u : R) • (Y : A)) (j : ℕ) :
    Module.End.eigenspace σ.toLinearEquiv.toLinearMap 1 ≃ₗ[R]
      Module.End.eigenspace σ.toLinearEquiv.toLinearMap ((u : R)^j) := by
  have hpow : σ ((Y : A)^j) = (u : R)^j • (Y : A)^j := by
    rw [map_pow, hY, smul_pow]
  have hinv : σ (((Y⁻¹ : Aˣ) : A)^j) = ((↑(u⁻¹) : R)^j) • (↑(Y⁻¹) : A)^j := by
    let V := Units.map σ.toAlgHom.toMonoidHom Y
    let W := Units.map (algebraMap R A).toMonoidHom u * Y
    have hVW : V = W := Units.ext (by simpa [V, W, Algebra.smul_def] using hY)
    have hwi := congrArg (fun v : Aˣ => (↑(v⁻¹) : A)) hVW
    change σ (↑(Y⁻¹) : A) = _ at hwi
    rw [map_pow, hwi]
    simp [W, Algebra.smul_def, mul_pow, mul_comm]
  exact
    { toFun := fun x => ⟨x.val * (Y : A)^j, by
        have hx := Module.End.mem_eigenspace_iff.mp x.property
        change σ x.val = (1 : R) • x.val at hx
        rw [one_smul] at hx
        apply Module.End.mem_eigenspace_iff.mpr
        change σ (_ * _) = _
        rw [map_mul, hx, hpow, mul_smul_comm]⟩
      invFun := fun x => ⟨x.val * (↑(Y⁻¹) : A)^j, by
        have hx := Module.End.mem_eigenspace_iff.mp x.property
        change σ x.val = (u : R)^j • x.val at hx
        apply Module.End.mem_eigenspace_iff.mpr
        change σ (_ * _) = _
        rw [map_mul, hx, hinv, smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_pow,
          Units.mul_inv, one_pow]⟩
      left_inv := fun x => Subtype.ext (by
        change _ * _ * _ = _
        rw [mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one])
      right_inv := fun x => Subtype.ext (by
        change _ * _ * _ = _
        rw [mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one])
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r x => Subtype.ext (smul_mul_assoc _ _ _) }

@[simp] theorem primeAxisEigenspaceEquiv_apply (σ : A ≃ₐ[R] A) (u : Rˣ) (Y : Aˣ)
    (hY : σ (Y : A) = (u : R) • (Y : A)) (j : ℕ)
    (x : Module.End.eigenspace σ.toLinearEquiv.toLinearMap 1) :
    ((primeAxisEigenspaceEquiv σ u Y hY j x : _) : A) = (x : A) * (Y : A)^j := rfl

@[simp] theorem primeAxisEigenspaceEquiv_symm_apply (σ : A ≃ₐ[R] A) (u : Rˣ) (Y : Aˣ)
    (hY : σ (Y : A) = (u : R) • (Y : A)) (j : ℕ)
    (x : Module.End.eigenspace σ.toLinearEquiv.toLinearMap ((u : R)^j)) :
    (((primeAxisEigenspaceEquiv σ u Y hY j).symm x : _) : A) =
      (x : A) * (↑(Y⁻¹) : A)^j := rfl

/-- The pair `Y^j,U*Y^j` forms a basis of the `u^j`-eigenspace whenever
`1,U` is a basis of the fixed submodule. -/
theorem exists_primeAxisEigenspace_basis (σ : A ≃ₐ[R] A) (u : Rˣ) (Y : Aˣ)
    (hY : σ (Y : A) = (u : R) • (Y : A)) (U : A)
    (b : Basis (Fin 2) R (Module.End.eigenspace σ.toLinearEquiv.toLinearMap 1))
    (h₀ : (b 0 : A) = 1) (h₁ : (b 1 : A) = U) (j : ℕ) :
    ∃ e : Basis (Fin 2) R (Module.End.eigenspace σ.toLinearEquiv.toLinearMap ((u : R)^j)),
      (e 0 : A) = (Y : A)^j ∧ (e 1 : A) = U * (Y : A)^j := by
  refine ⟨b.map (primeAxisEigenspaceEquiv σ u Y hY j), ?_, ?_⟩ <;>
    simp [h₀, h₁]

end FiniteFourier
end LinearAlgebra
end OAI
