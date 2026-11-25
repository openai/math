import OAI.Computability.BorderVNP.BranchFieldEmbedding
import OAI.Computability.BorderVNP.BranchCurveParameterCoefficients
import OAI.Computability.BorderVNP.BranchCurveModel
import OAI.Computability.BorderVNP.BranchCurveBoxRatio

/-!
# The affine equations on the constructed function field

The same parameter in the base field and in the evaluated affine coordinates
gives the original polynomial equations and their Jacobian on the branch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial Residue.JetRing

variable {K L σ : Type*} [Field K] [Field L]

/-- The generic row is the coefficient embedding of the equation with its
distinguished variable transferred to the univariate coefficient ring. -/
theorem genericRow_parameter (p : MvPolynomial (Option σ) K) :
    genericRow p = map (algebraMap (Polynomial K) (DeformationField K)) (optionEquivRight K σ p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [genericRow, eval₂Hom_C, RingHom.comp_apply, optionEquivRight_C, map_C]
    exact congrArg C (IsScalarTower.algebraMap_apply K (Polynomial K) (DeformationField K) c)
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, hp, map_mul, map_mul]
    cases j <;> simp only [genericRow, eval₂Hom_X', optionEquivRight_X_none,
      optionEquivRight_X_some, Option.elim_some, Option.elim_none, map_X, map_C]

/-- Evaluating a generic row in any extension of the rational parameter field
agrees with ordinary evaluation of the full affine equation. -/
theorem genericRow_eval [Algebra (DeformationField K) L] (x : σ → L) (p : MvPolynomial (Option σ) K) :
    let φ := (algebraMap (DeformationField K) L).comp (algebraMap (Polynomial K) (DeformationField K))
    aeval x (genericRow p) = eval₂Hom (φ.comp Polynomial.C) (fun i => i.elim (φ Polynomial.X) x) p := by
  intro φ
  rw [genericRow_parameter, aeval_def, eval₂_map]
  exact eval_parameter_coefficients φ x p

/-- The chart parameter and original affine parameters satisfy the equations
with invertible Jacobian in the function field of the constructed branch. -/
theorem branch_affine_equations {h : ℕ} {I : Type*} {Y : I → MvPolynomial (Fin h) K}
    {c : I → K} {g : Fin h → MvPolynomial (Option (Fin h)) K}
    (B : GeometricBranch Y c (fun i => genericRow (g i))) :
    let φ := (algebraMap (DeformationField K) B.L).comp (algebraMap (Polynomial K) (DeformationField K))
    let v := eval₂Hom (φ.comp Polynomial.C) (fun i : Option (Fin h) => i.elim (φ Polynomial.X) B.x)
    (∀ i, v (g i) = 0) ∧ v (boxJacobian g) ≠ 0 := by
  intro φ v
  have ev (p : MvPolynomial (Option (Fin h)) K) : aeval B.x (genericRow p) = v p :=
    genericRow_eval B.x p
  refine ⟨fun i => (ev _).symm.trans (B.root i), ?_⟩
  change eval₂Hom _ _ (boxJacobian g) ≠ 0
  rw [eval_boxJacobian]
  have mat : chartJacobian (φ.comp Polynomial.C) (fun i : Option (Fin h) => i.elim (φ Polynomial.X) B.x) g =
      Matrix.of fun i j => aeval B.x (pderiv j (genericRow (g i))) := by
    ext i j
    change v (pderiv (some j) (g i)) = aeval B.x (pderiv j (genericRow (g i)))
    rw [← ev, genericRow_parameter, genericRow_parameter, pderiv_map, parameter_pderiv]
  rw [mat]
  exact B.jacobian

end Branch

end BorderVNP
end Computability
end OAI
