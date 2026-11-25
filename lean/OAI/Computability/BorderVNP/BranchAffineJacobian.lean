import OAI.Computability.BorderVNP.BranchJacobianGeneric
import OAI.Computability.BorderVNP.BranchChartIndependent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # The Jacobian in the original affine parameters

The cleared deformation equations are expressed in the original affine coordinates.
At a root their Jacobian differs by a nonzero row factor from the quotient-rule matrix
of the displacement map. Its leading term in the deformation parameter is the chart
change. At a single coordinate point this chart change is diagonal with entries `±1`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial
open scoped Matrix

variable {K T L : Type*} [Field K] [Field T] [Field L] [Algebra K T] [Algebra T L] {m : ℕ}

/-- Original-affine-coordinate denominator for chart `k`. -/
noncomputable def affineChartDen (k : Option (Fin m)) : MvPolynomial (Fin m) K := k.elim 1 X

/-- Original-affine-coordinate numerator of the `j`th independent chart variable. -/
noncomputable def affineChartNum (k : Option (Fin m)) (j : Fin m) : MvPolynomial (Fin m) K :=
  (chartIndex k j).elim 1 X

/-- The chart numerator and denominator degrees in the affine parameters. -/
theorem affineChart_degrees (k : Option (Fin m)) :
    (affineChartDen (K := K) k).totalDegree ≤ 1 ∧
      ∀ j, (affineChartNum (K := K) k j).totalDegree ≤ 1 := by
  constructor
  · cases k <;> simp [affineChartDen]
  · intro j
    rcases h : chartIndex k j with _ | i <;> simp [affineChartNum, h]

omit [Algebra K T] in
private theorem generic_two_matrix (inc : K →+* T) (lift : Polynomial K →+* T)
    (hi : Function.Injective lift) (hc : ∀ k, lift (Polynomial.C k) = inc k)
    (A B : Matrix (Fin m) (Fin m) K) (hB : B.det ≠ 0) :
    (inc.mapMatrix A + (lift Polynomial.X) • inc.mapMatrix B).det ≠ 0 := by
  let t := lift Polynomial.X
  have hfactor : inc.mapMatrix A + t • inc.mapMatrix B =
      (Matrix.scalar (Fin m) t + inc.mapMatrix (A*B⁻¹)) * inc.mapMatrix B := by
    rw [add_mul, ← map_mul, B.nonsing_inv_mul_cancel_right _ (isUnit_iff_ne_zero.mpr hB), add_comm]
    congr 1
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  rw [hfactor, Matrix.det_mul, ← RingHom.map_det]
  exact mul_ne_zero (determinant_generic_scalar inc lift hi hc _) ((map_ne_zero_iff inc inc.injective).mpr hB)

private theorem chart_jacobian_at_axis (k : Option (Fin m)) :
    let z : Fin m → K := fun i => if k = some i then 1 else 0
    (eval z).mapMatrix (jacobianNumerator 0 (affineChartDen k) (affineChartNum k)) =
      Matrix.diagonal (fun i => if k = some i then (-1 : K) else 1) := by
  intro z
  ext i j
  cases k with
  | none =>
    by_cases h : i = j <;> simp [jacobianNumerator, affineChartDen, affineChartNum, chartIndex,
      Matrix.scalar, Matrix.diagonal, Pi.single_apply, h]
  | some k =>
    by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hij : i = j <;>
      simp_all [jacobianNumerator, affineChartDen, affineChartNum, chartIndex,
        Matrix.scalar, Matrix.diagonal, Pi.single_apply, z, eq_comm]

/-- Determinant numerator for `Aᵢ(x) / den(x) + t zᵢ(x)`, written in the original
affine variables. -/
noncomputable def affineDisplacementJacobian (k : Option (Fin m)) (t : T)
    (A : Fin m → MvPolynomial (Fin m) T) : MvPolynomial (Fin m) T :=
  (jacobianNumerator 0 (affineChartDen k) (fun i => A i + C t * affineChartNum k i)).det

private theorem affine_displacement_pencil (k : Option (Fin m)) (t : T) (z : Fin m → K)
    (A : Fin m → MvPolynomial (Fin m) K) :
    let inc := algebraMap K T
    (eval (inc ∘ z)).mapMatrix (jacobianNumerator 0 (affineChartDen k)
      (fun i => map inc (A i) + C t * affineChartNum k i)) =
      inc.mapMatrix ((eval z).mapMatrix (jacobianNumerator 0 (affineChartDen k) A)) +
      t • inc.mapMatrix ((eval z).mapMatrix (jacobianNumerator 0 (affineChartDen k) (affineChartNum k))) := by
  intro inc
  have hd : map inc (affineChartDen (K := K) k) = affineChartDen (K := T) k := by
    cases k <;> simp [affineChartDen]
  have hn (i) : map inc (affineChartNum (K := K) k i) = affineChartNum (K := T) k i := by
    cases he : chartIndex k i <;> simp [affineChartNum, he]
  ext i j
  simp only [jacobianNumerator, map_zero, zero_mul, Matrix.scalar, zero_add,
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, map_sub, map_mul, map_add, pderiv_C_mul, eval_C]
  rw [← hd, ← hn, pderiv_map, pderiv_map, pderiv_map]
  simp only [← map_eval]
  ring

/-- The actual affine-coordinate displacement determinant is a nonzero polynomial over
the rational deformation field, in every characteristic. -/
theorem affineDisplacementJacobian_generic [Algebra (Polynomial K) T] [IsScalarTower K (Polynomial K) T]
    [IsFractionRing (Polynomial K) T] (k : Option (Fin m)) (A : Fin m → MvPolynomial (Fin m) K) :
    affineDisplacementJacobian k (algebraMap (Polynomial K) T Polynomial.X)
      (fun i => map (algebraMap K T) (A i)) ≠ 0 := by
  let z : Fin m → K := fun i => if k = some i then 1 else 0
  let inc := algebraMap K T
  let lift := algebraMap (Polynomial K) T
  have hB : ((eval z).mapMatrix (jacobianNumerator 0 (affineChartDen k) (affineChartNum k))).det ≠ 0 := by
    rw [chart_jacobian_at_axis (K := K) k, Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    split <;> simp
  have hn := generic_two_matrix inc lift (IsFractionRing.injective _ _)
    (fun a => (IsScalarTower.algebraMap_apply K (Polynomial K) T a).symm)
    ((eval z).mapMatrix (jacobianNumerator 0 (affineChartDen k) A)) _ hB
  intro hz
  have h := congrArg (eval (inc ∘ z)) hz
  change eval (inc ∘ z) (jacobianNumerator 0 (affineChartDen k)
    (fun i => map inc (A i) + C (lift Polynomial.X) * affineChartNum k i)).det = _ at h
  rw [RingHom.map_det, affine_displacement_pencil, map_zero] at h
  exact hn h

/-- A degree bound on the affine displacement determinant, independent of the target. -/
theorem affineDisplacementJacobian_degree (k : Option (Fin m)) (t : T)
    (A : Fin m → MvPolynomial (Fin m) T) {d : ℕ} (hd : 1 ≤ d) (hA : ∀ i, (A i).totalDegree ≤ d) :
    (affineDisplacementJacobian k t A).totalDegree ≤ m*(2*d) := by
  obtain ⟨hb, hn⟩ := affineChart_degrees (K := T) k
  have h (i) : (A i + C t * affineChartNum k i).totalDegree ≤ d := by
    apply (totalDegree_add ..).trans (max_le (hA i) _)
    exact (totalDegree_mul ..).trans (by simpa using (hn i).trans hd)
  simpa [affineDisplacementJacobian] using jacobianNumerator_det_degree 0 _ _ (hb.trans hd) h

/-- The original affine row after clearing the common chart denominator. -/
noncomputable def affineRow (k : Option (Fin m)) (t : T) (A : Fin m → MvPolynomial (Fin m) T)
    (v : Fin m → T) (i : Fin m) : MvPolynomial (Fin m) T :=
  A i + C t * affineChartNum k i - C (t*v i) * affineChartDen k

/-- Nonvanishing of the target-independent numerator at a root gives a nonsingular
Jacobian for the actual cleared affine equations. -/
theorem nonsingular_affineRow (k : Option (Fin m)) (t : T) (A : Fin m → MvPolynomial (Fin m) T)
    (v : Fin m → T) (x : Fin m → L) (hroot : ∀ i, aeval x (affineRow k t A v i) = 0)
    (hn : aeval x (affineDisplacementJacobian k t A) ≠ 0) :
    (Matrix.of fun i j => aeval x (pderiv j (affineRow k t A v i))).det ≠ 0 := by
  let P := fun i => A i + C t * affineChartNum k i
  let den := affineChartDen (K := T) k
  have hr (i) : aeval x (P i) = algebraMap T L (t*v i) * aeval x den := by
    have h := hroot i
    change aeval x (P i - C _ * den) = 0 at h
    simpa only [map_sub, map_mul, aeval_C, sub_eq_zero] using h
  have he : (aeval x).mapMatrix (jacobianNumerator 0 den P) =
      (aeval x den) • (Matrix.of fun i j => aeval x (pderiv j (affineRow k t A v i))) := by
    ext i j
    change _ = _ * aeval x (pderiv j (P i - C (t*v i) * den))
    rw [(pderiv j).map_sub, pderiv_C_mul]
    simp only [jacobianNumerator, map_zero, zero_mul, Matrix.scalar, zero_add, AlgHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.of_apply, map_sub, map_mul, aeval_C, hr]
    ring
  change aeval x (jacobianNumerator 0 den P).det ≠ 0 at hn
  rw [(aeval x).map_det, he, Matrix.det_smul] at hn
  exact (mul_ne_zero_iff.mp hn).2

end Branch

end BorderVNP
end Computability
end OAI
