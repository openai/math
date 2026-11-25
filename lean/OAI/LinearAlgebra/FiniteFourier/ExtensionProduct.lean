import OAI.Computability.FourierCircuit.Triangular
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic

/-! # Fixed scalar multiplication in a power basis

For an ordinary product of degree below twice the modulus degree, the reversed
high coefficients give the quotient via a fixed truncated reciprocal.  This
realizes power-basis reduction using fixed polynomial convolutions.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped PowerSeries Classical

noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Reverse the high coefficients, multiply by the fixed reciprocal of the
reversed modulus to precision `e`, and reverse the quotient back. -/
def reciprocalQuotient (e : ℕ) (m y : K[X]) : K[X] :=
  reflect (e - 1) (PowerSeries.trunc e
    (((m.reflect e : K[X]) : K⟦X⟧)⁻¹ * (y.reflect (e + (e - 1)) : K[X])))

/-- The reversed-series computation recovers the Euclidean quotient, for any
monic modulus of positive degree and any dividend of degree below twice that. -/
theorem reciprocalQuotient_eq_divByMonic {e : ℕ} (he : 0 < e) {m : K[X]}
    (hm : m.Monic) (hdeg : m.natDegree = e) (y : K[X]) (hy : y.natDegree < 2 * e) :
    reciprocalQuotient e m y = y /ₘ m := by
  let Q := y /ₘ m
  let R := y %ₘ m
  have hq : Q.natDegree ≤ e - 1 := by
    dsimp [Q]; rw [natDegree_divByMonic y hm, hdeg]; omega
  have hr : R.natDegree < e := by
    have hne : m ≠ 1 := fun h ↦ by simp [h] at hdeg; omega
    exact (natDegree_modByMonic_lt y hm hne).trans_eq hdeg
  let f : K⟦X⟧ := (m.reflect e : K[X])
  have hf : f.constantCoeff ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    change PowerSeries.coeff 0 (m.reflect e : K⟦X⟧) ≠ 0
    rw [Polynomial.coeff_coe, coeff_reflect, revAt_zero, ← hdeg, hm.coeff_natDegree]
    exact one_ne_zero
  have hrem : PowerSeries.trunc e ((R.reflect (e + (e - 1)) : K[X]) : K⟦X⟧) = 0 := by
    ext k
    rw [PowerSeries.coeff_trunc]
    by_cases hk : k < e
    · simp only [hk, ite_true, Polynomial.coeff_coe, coeff_reflect, coeff_zero]
      rw [revAt_le (by omega)]
      apply coeff_eq_zero_of_natDegree_lt
      omega
    · simp [hk]
  have hhigh : PowerSeries.trunc e ((y.reflect (e + (e - 1)) : K[X]) : K⟦X⟧) =
      PowerSeries.trunc e (f * (Q.reflect (e - 1) : K⟦X⟧)) := by
    conv_lhs => rw [← modByMonic_add_div y m]
    rw [reflect_add, reflect_mul _ _ hdeg.le hq, Polynomial.coe_add, map_add, hrem,
      zero_add, Polynomial.coe_mul]
  have hqr : (Q.reflect (e - 1)).natDegree < e :=
    natDegree_reflect_le.trans_lt (max_lt (by omega) (by omega))
  have hs : PowerSeries.trunc e (f⁻¹ * (y.reflect (e + (e - 1)) : K⟦X⟧)) = Q.reflect (e - 1) := by
    rw [← PowerSeries.trunc_mul_trunc, hhigh, PowerSeries.trunc_mul_trunc,
      ← mul_assoc, PowerSeries.inv_mul_cancel _ hf, one_mul, PowerSeries.trunc_coe_eq_self hqr]
  rw [reciprocalQuotient, hs, reflect_reflect]

/-- The output subtraction is the remainder of the ordinary product by the
fixed minimal polynomial. -/
def fixedProductReduction (e : ℕ) (m s x : K[X]) : K[X] :=
  let y := s * x
  y - m * reciprocalQuotient e m y

theorem fixedProductReduction_eq_modByMonic {e : ℕ} (he : 0 < e) {m s x : K[X]}
    (hm : m.Monic) (hd : m.natDegree = e) (hs : s.natDegree < e) (hx : x.natDegree < e) :
    fixedProductReduction e m s x = (s * x) %ₘ m := by
  have hprod : (s * x).natDegree ≤ s.natDegree + x.natDegree := natDegree_mul_le
  rw [fixedProductReduction, reciprocalQuotient_eq_divByMonic he hm hd _ (by omega),
    modByMonic_eq_sub_mul_div]

/-- For a prescribed scalar in a finite simple extension, choose its polynomial
in the power basis. The three fixed multiplications compute the scalar product
in that same basis for every input polynomial of degree below the dimension. -/
theorem powerBasis_fixedProductReduction (pb : PowerBasis K E) (u : E) :
    ∃ s : K[X], s.natDegree < pb.dim ∧ aeval pb.gen s = u ∧
      ∀ x : K[X], x.natDegree < pb.dim →
        let r := fixedProductReduction pb.dim (minpoly K pb.gen) s x
        r.natDegree < pb.dim ∧ aeval pb.gen r = u * aeval pb.gen x := by
  obtain ⟨s, hs, hsu⟩ := pb.exists_eq_aeval u
  refine ⟨s, hs, hsu.symm, ?_⟩
  intro x hx
  have hm := minpoly.monic pb.isIntegral_gen
  have hd := pb.natDegree_minpoly
  have hm1 : minpoly K pb.gen ≠ 1 := fun h ↦ by simp [h] at hd; exact pb.dim_ne_zero hd.symm
  dsimp only
  rw [fixedProductReduction_eq_modByMonic pb.dim_pos hm hd hs hx]
  refine ⟨(natDegree_modByMonic_lt _ hm hm1).trans_eq hd, ?_⟩
  rw [aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _), map_mul, ← hsu]

open ExactFourier.CoefficientTime

private lemma truncMatrix_coeff_apply (n : ℕ) (f g : K⟦X⟧) (i : Fin n) :
    (truncMatrix n f).mulVec (fun j : Fin n ↦ PowerSeries.coeff j.val g) i =
      PowerSeries.coeff i.val (f * g) :=
  (coeff_mul_truncated f g i).symm

/-- Three fixed lower triangular Toeplitz products, with zero padding and two
reversals. The ordinary product uses precision `2e`; the reciprocal and
quotient corrections each use precision `e`. -/
def fixedScalarCoordinates (e : ℕ) (m s : K[X]) (x : Fin e → K) : Fin e → K :=
  let y := (truncMatrix (2 * e) (s : K⟦X⟧)).mulVec
    (fun j ↦ if h : j.val < e then x ⟨j, h⟩ else 0)
  let reversedHigh := fun i : Fin e ↦ y ⟨e + (e - 1) - i.val, by have := i.isLt; omega⟩
  let qRev := (truncMatrix e ((m.reflect e : K⟦X⟧)⁻¹)).mulVec reversedHigh
  let correction := (truncMatrix e (m : K⟦X⟧)).mulVec (fun j ↦ qRev j.rev)
  fun i ↦ y ⟨i.val, by have := i.isLt; omega⟩ - correction i

theorem fixedScalarCoordinates_eq (e : ℕ) (m s : K[X]) (x : Fin e → K) (i : Fin e) :
    fixedScalarCoordinates e m s x i =
      (fixedProductReduction e m s (ofFn e x)).coeff i.val := by
  let Xp := ofFn e x
  let Y := s * Xp
  let f : K⟦X⟧ := (m.reflect e : K⟦X⟧)⁻¹
  let G : K⟦X⟧ := (Y.reflect (e + (e - 1)) : K[X])
  let Qrev := PowerSeries.trunc e (f * G)
  let Q := Qrev.reflect (e - 1)
  have hpad (j : Fin (2 * e)) :
      (if h : j.val < e then x ⟨j.val, h⟩ else 0) = PowerSeries.coeff j.val (Xp : K⟦X⟧) := by
    rw [Polynomial.coeff_coe]
    split_ifs with h
    · exact (ofFn_coeff_eq_val_of_lt x h).symm
    · exact (ofFn_coeff_eq_zero_of_ge x (by omega)).symm
  have hy (j : Fin (2 * e)) :
      (truncMatrix (2 * e) (s : K⟦X⟧)).mulVec
        (fun k ↦ if h : k.val < e then x ⟨k, h⟩ else 0) j = Y.coeff j.val := by
    simp_rw [hpad]
    rw [truncMatrix_coeff_apply, ← Polynomial.coe_mul, Polynomial.coeff_coe]
  have hhigh (j : Fin e) : Y.coeff (e + (e - 1) - j.val) = PowerSeries.coeff j.val G := by
    rw [show G = (Y.reflect (e + (e - 1)) : K⟦X⟧) from rfl, Polynomial.coeff_coe,
      coeff_reflect, revAt_le (by have := j.isLt; omega)]
  have hq (j : Fin e) : PowerSeries.coeff j.rev.val (f * G) = PowerSeries.coeff j.val (Q : K⟦X⟧) := by
    rw [Polynomial.coeff_coe, show Q = Qrev.reflect (e - 1) from rfl, coeff_reflect,
      revAt_le (by have := j.isLt; omega)]
    simp [Qrev, PowerSeries.coeff_trunc, Fin.val_rev, show e - (j.val + 1) = e - 1 - j.val by omega, show e - 1 - j.val < e by have := j.isLt; omega]
  unfold fixedScalarCoordinates
  simp_rw [hy, hhigh]
  change Y.coeff i.val - (truncMatrix e (m : K⟦X⟧)).mulVec
      (fun j ↦ (truncMatrix e f).mulVec (fun k : Fin e ↦ PowerSeries.coeff k.val G) j.rev) i = _
  simp_rw [truncMatrix_coeff_apply, hq]
  rw [truncMatrix_coeff_apply, ← Polynomial.coe_mul, Polynomial.coeff_coe]
  exact (coeff_sub Y (m * Q) i.val).symm

private theorem repr_aeval_of_lt (pb : PowerBasis K E) (x : K[X]) (hx : x.natDegree < pb.dim)
    (i : Fin pb.dim) : pb.basis.repr (aeval pb.gen x) i = x.coeff i.val := by
  rw [aeval_eq_sum_range' hx, ← Fin.sum_univ_eq_sum_range]
  simp only [← pb.basis_eq_pow, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  simp

/-- The base-field matrix for multiplication by a prescribed extension scalar
is realized by the three Toeplitz calls in `fixedScalarCoordinates`. -/
theorem powerBasis_scalar_coordinates (pb : PowerBasis K E) (u : E) :
    ∃ s : K[X], s.natDegree < pb.dim ∧ ∀ x : Fin pb.dim → K, ∀ i : Fin pb.dim,
      fixedScalarCoordinates pb.dim (minpoly K pb.gen) s x i =
        pb.basis.repr (u * ∑ j, x j • pb.basis j) i := by
  obtain ⟨s, hs, _, h⟩ := powerBasis_fixedProductReduction pb u
  refine ⟨s, hs, fun x i ↦ ?_⟩
  let Xp := ofFn pb.dim x
  have hx : Xp.natDegree < pb.dim := ofFn_natDegree_lt pb.dim_pos x
  have hx' : aeval pb.gen Xp = ∑ j, x j • pb.basis j := by
    rw [aeval_eq_sum_range' hx, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp [Xp, Algebra.smul_def, pb.basis_eq_pow, ofFn_coeff_eq_val_of_lt x j.isLt]
  obtain ⟨hr, he⟩ := h Xp hx
  rw [fixedScalarCoordinates_eq, ← repr_aeval_of_lt pb _ hr i, he, hx']

end

end FiniteFourier
end LinearAlgebra
end OAI
