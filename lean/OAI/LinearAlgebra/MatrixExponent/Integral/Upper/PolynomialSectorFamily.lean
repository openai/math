import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialSectors
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialWeightFamily

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# The polynomial witness for the three-sector degeneration

Every coefficient has degree at most one.  Its constant coefficient is the
entire shared-first-input sector assembly.  At each nonzero parameter the
evaluated tensor is an actual restriction of the original polynomial tensor.
These explicit facts support interpolation without assuming that an arbitrary
tensor character preserves topological limits.
-/

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper

/-- The same family as the diagonal degeneration, expressed in the complete
sector bases on the last two legs.  The first input is unchanged. -/
def triplingPolynomialFamily (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Tensor (Polynomial O) (Fin a) (TriplingY a h) (TriplingZ a h) :=
  Tensor.pullback id (triplingYEquiv a h ha hh) (triplingZEquiv a h ha hh)
    (weightedPolynomial (polynomialTensor a (triplingWidth a h))
      (fun _ => 0) (fun y => triplingYWeight a h y.val)
      (fun z => triplingZWeight a h z.val))

private theorem tripling_source_weights_nonneg (a h : ℕ) (ha : 1 ≤ a)
    (x : Fin a) (y : Fin (triplingWidth a h))
    (z : Fin (a + triplingWidth a h - 1))
    (hc : polynomialTensor a (triplingWidth a h) x y z ≠ 0) :
    0 ≤ (0 : ℤ) + triplingYWeight a h y.val + triplingZWeight a h z.val := by
  have hs : x.val + y.val = z.val := by
    by_contra hn
    exact hc (by simp [polynomialTensor, hn])
  simpa using tripling_weight_nonneg ha x.isLt hs

private theorem tripling_weights_toNat_le_one (a h y z : ℕ) :
    ((0 : ℤ) + triplingYWeight a h y + triplingZWeight a h z).toNat ≤ 1 := by
  unfold triplingYWeight triplingZWeight
  split_ifs <;> decide

/-- The constant coefficient retains all three branches, including their
vanishing cross-sector coefficients, in one shared first-input basis. -/
theorem triplingPolynomialFamily_coeff_zero (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (y : TriplingY a h) (z : TriplingZ a h) :
    (triplingPolynomialFamily a h ha hh x y z).coeff 0 = triplingSectorTensor a h x y z := by
  change (weightedPolynomial (polynomialTensor a (triplingWidth a h))
      (fun _ => 0) (fun y => triplingYWeight a h y.val)
      (fun z => triplingZWeight a h z.val) x
      (triplingYEquiv a h ha hh y) (triplingZEquiv a h ha hh z)).coeff 0 = _
  rw [weightedPolynomial_coeff_zero _ _ _ _ (tripling_source_weights_nonneg a h ha)]
  exact congrFun (congrFun (congrFun (triplingGraded_sector_assembly a h ha hh) x) y) z

/-- There is no growing or unspecified approximation degree: every coordinate
of this explicit family has degree at most one. -/
theorem triplingPolynomialFamily_degree_le (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (y : TriplingY a h) (z : TriplingZ a h) :
    (triplingPolynomialFamily a h ha hh x y z).degree ≤ (1 : ℕ) := by
  exact weightedPolynomial_degree_le (polynomialTensor a (triplingWidth a h))
    (fun _ => 0) (fun y => triplingYWeight a h y.val)
    (fun z => triplingZWeight a h z.val) (D := 1)
    (fun _ y z _ => tripling_weights_toNat_le_one a h y.val z.val)
    x (triplingYEquiv a h ha hh y) (triplingZEquiv a h ha hh z)

/-- Every nonzero evaluation is an exact restriction of the original source
tensor. The sector reindexing is one fixed pair of local maps, with identity
on the common first input, after the diagonal maps. -/
theorem triplingPolynomialFamily_eval_mem_restrictionOrbit
    (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) {t : O} (ht : IsUnit t) :
    (fun x y z => (triplingPolynomialFamily a h ha hh x y z).eval t) ∈
      LocalTensor.orbit (polynomialTensor a (triplingWidth a h)) := by
  classical
  let E : Tensor O (Fin a) (Fin (triplingWidth a h))
      (Fin (a + triplingWidth a h - 1)) :=
    fun x y z => (weightedPolynomial (polynomialTensor a (triplingWidth a h))
      (fun _ => 0) (fun y => triplingYWeight a h y.val)
      (fun z => triplingZWeight a h z.val) x y z).eval t
  have hE : E ∈ LocalTensor.orbit (polynomialTensor a (triplingWidth a h)) :=
    weightedPolynomial_eval_mem_restrictionOrbit _ _ _ _
      (tripling_source_weights_nonneg a h ha) ht
  have hr := LocalTensor.restrict_mem hE
    (fun (x' x : Fin a) => if x = x' then (1 : O) else 0)
    (fun (y' : TriplingY a h) (y : Fin (triplingWidth a h)) =>
      if y = triplingYEquiv a h ha hh y' then (1 : O) else 0)
    (fun (z' : TriplingZ a h) (z : Fin (a + triplingWidth a h - 1)) =>
      if z = triplingZEquiv a h ha hh z' then (1 : O) else 0)
  have hp : Tensor.pullback (id : Fin a → Fin a)
      (triplingYEquiv a h ha hh) (triplingZEquiv a h ha hh) E =
      (fun x y z => (triplingPolynomialFamily a h ha hh x y z).eval t) := rfl
  rw [Tensor.pullback_eq_restrict] at hp
  simp only [id_eq] at hp
  rw [hp] at hr
  exact hr

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
