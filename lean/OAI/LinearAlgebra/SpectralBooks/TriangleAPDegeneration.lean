import OAI.LinearAlgebra.SpectralBooks.GeometricRestriction
import OAI.LinearAlgebra.SpectralBooks.TriangleAPFormat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Specializing the wire triangle to arithmetic-progression support

The square `(i - 2j + k)²` splits into three integer weights, each depending
only on the two edge labels at one site. The local Laurent weights give a
polynomial path on the support of the triangle tensor. Its value at zero
retains exactly the arithmetic progressions, in every characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Polynomial

section

open scoped Classical

/-- For a sum of coordinate basis tensors, locally additive integer weights
with nonnegative total on each term specialize to the terms of total weight zero. -/
theorem basisTensor_zeroWeight_mem_closure (K : Type*) [Field K] [Infinite K]
    {I J : Type*} [Fintype I] [Fintype J] {A : I → Type*} [∀ i, Fintype (A i)]
    (a : J → ∀ i, A i) (w : ∀ i, A i → ℤ) (hw : ∀ j, 0 ≤ ∑ i, w i (a j i)) :
    (fun x ↦ ∑ j, if x = a j ∧ ∑ i, w i (a j i) = 0 then 1 else 0) ∈
      affineZariskiClosure {Y | Crossing.IsRestriction Y (Crossing.basisTensor (F := K) a)} := by
  classical
  let e (j : J) : ℤ := ∑ i, w i (a j i)
  let P (x : ∀ i, A i) : K[X] := ∑ j, if x = a j then X ^ (e j).toNat else 0
  have ht (t : K) (ht : t ≠ 0) : (fun x ↦ (P x).eval t) ∈
      {Y | Crossing.IsRestriction Y (Crossing.basisTensor (F := K) a)} := by
    apply (Crossing.restriction_basisTensor_iff _ _).mpr
    refine ⟨fun i b c ↦ if b = c then t ^ w i c else 0, fun x ↦ ?_⟩
    simp only [P, Polynomial.eval_finsetSum, Fintype.prod_ite_zero]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : x = a j
    · subst x
      simp only [ite_true, eval_X_pow, ← zpow_natCast, e, Int.toNat_of_nonneg (hw j)]
      rw [ite_eq_left_of_eq_true _ _ (propext ⟨fun _ ↦ trivial, fun _ _ ↦ trivial⟩)]
      exact Finset.induction_on (motive := fun s ↦ t ^ (∑ i ∈ s, w i (a j i)) =
        ∏ i ∈ s, t ^ w i (a j i)) Finset.univ (by simp) (fun i s hi ih ↦ by
          simp [hi, zpow_add₀ ht, ih])
    · simp [h, ← funext_iff]
  have hzero (x : ∀ i, A i) : (P x).eval 0 =
      ∑ j, if x = a j ∧ ∑ i, w i (a j i) = 0 then 1 else 0 := by
    simp only [P, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hx : x = a j
    · by_cases he : e j = 0
      · have he' : ∑ i, w i (a j i) = 0 := he
        simp [hx, he, he']
      · have hpos : (e j).toNat ≠ 0 := by have hh := hw j; change 0 ≤ e j at hh; omega
        simp [hx, zero_pow hpos, ← show e j = ∑ i, w i (a j i) from rfl, he]
    · simp [hx]
  rw [← funext hzero]
  exact polynomialCurve_zero_mem_affineZariskiClosure P ht

/-- The three weights sum to a square on every term of the triangle tensor. -/
private def triangleAPWeight (q : ℕ) : Fin 3 → Fin q × Fin q → ℤ :=
  ![fun x ↦ ((x.1.val : ℤ) - 2 * x.2.val) ^ 2,
    fun x ↦ (x.2.val : ℤ) ^ 2 - 4 * x.1.val * x.2.val,
    fun x ↦ 2 * (x.1.val : ℤ) * x.2.val]

private theorem triangleAPWeight_sum {q : ℕ} (s : Fin q × Fin q × Fin q) :
    ∑ i, triangleAPWeight q i (triangleWireTerm q s i) =
      ((s.1.val : ℤ) - 2 * s.2.1.val + s.2.2.val) ^ 2 := by
  rw [Fin.sum_univ_three]
  change ((s.1.val : ℤ) - 2 * s.2.1.val) ^ 2 +
    ((s.2.2.val : ℤ) ^ 2 - 4 * s.2.1.val * s.2.2.val) +
    2 * (s.2.2.val : ℤ) * s.1.val = _
  ring

/-- The AP tensor belongs to the restriction closure of the wire triangle. -/
theorem triangleAPTensor_mem_restrictionClosure (K : Type*) [Field K] [Infinite K] (q : ℕ) :
    triangleAPTensor K q ∈ affineZariskiClosure {Y | Crossing.IsRestriction Y
      (Crossing.basisTensor (F := K) (triangleWireTerm q))} := by
  have h := basisTensor_zeroWeight_mem_closure K (triangleWireTerm q) (triangleAPWeight q)
    (fun j ↦ triangleAPWeight_sum j ▸ sq_nonneg _)
  convert h using 1
  funext x
  simp [triangleAPTensor, triangleAPWeight_sum]

/-- This comparison is valid for every spectral point of the original field,
including finite fields, by descent from the algebraic closure. -/
theorem triangleAPTensor_value_le_wire (K : Type*) [Field K] (q : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : SiteTensor.TensorClass.{0} (Fin 3) K → _ → Prop)) :
    SiteTensor.coeffValue φ (triangleAPTensor K q) ≤ SiteTensor.coeffValue φ
      (Crossing.basisTensor (F := K) (triangleWireTerm q)) := by
  apply SiteTensor.coeffValue_le_of_geometric_restriction (E := AlgebraicClosure K)
  have ht : (fun b ↦ algebraMap K (AlgebraicClosure K) (triangleAPTensor K q b)) =
      triangleAPTensor (AlgebraicClosure K) q := by
    funext b
    simp [triangleAPTensor]
  have hs : (fun b ↦ algebraMap K (AlgebraicClosure K) (Crossing.basisTensor (triangleWireTerm q) b)) =
      Crossing.basisTensor (F := AlgebraicClosure K) (triangleWireTerm q) := by
    funext b
    simp [Crossing.basisTensor]
  rw [ht, hs]
  exact triangleAPTensor_mem_restrictionClosure (AlgebraicClosure K) q

end

end SpectralBooks
end LinearAlgebra
end OAI
