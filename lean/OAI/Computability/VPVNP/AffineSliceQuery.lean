import OAI.Computability.VPVNP.MacaulaySliceBasis

/-!
# Coefficient queries after prime reduction and affine slicing

A row lookup either asks for one original integer coefficient and casts it
to the base field, or reads the constant and linear coefficients of one of
the supplied affine cuts. This gives the scalar interface used by the
finite-slice coordinate queries of Appendix D.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex

open MvPolynomial

variable {t e s : ℕ} {K E : Type*} [Field K]

/-- One affine equation, represented by its coefficient words in the slice field. -/
structure AffineCut (t : ℕ) (K : Type*) where
  /-- Coefficient of the constant monomial in the affine slice equation over `K`. -/
  constant : K
  /-- Coefficient of each of the `t` coordinate variables in the affine slice equation. -/
  linear : Fin t → K

namespace AffineCut

/-- The multivariate polynomial of the affine equation, obtained by adding its constant term to
the weighted sum of the coordinate variables. -/
noncomputable def polynomial (cut : AffineCut t K) : MvPolynomial (Fin t) K :=
  C cut.constant + ∑ i, monomial (Finsupp.single i 1) (cut.linear i)

/-- Read the coefficient of a cut at a numeric exponent tuple. -/
def getCoeff (cut : AffineCut t K) (a : Fin t → ℕ) : K :=
  (if ∀ i, a i = 0 then cut.constant else 0) +
    ∑ i : Fin t, if ∀ j, a j = (if j = i then 1 else 0) then cut.linear i else 0

theorem getCoeff_eq (cut : AffineCut t K) (a : Fin t → ℕ) :
    cut.getCoeff a = cut.polynomial.coeff (exponentVector a) := by
  have hz : (∀ i, a i = 0) ↔ exponentVector a = 0 := by rw [DFunLike.ext_iff]; rfl
  have hs (i : Fin t) : (∀ j, a j = if j = i then 1 else 0) ↔
      Finsupp.single i 1 = exponentVector a := by
    rw [DFunLike.ext_iff]
    simp [exponentVector, Finsupp.single_apply, eq_comm]
  rw [getCoeff, polynomial, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C, coeff_sum]
  simp only [hz, hs, coeff_monomial, eq_comm (a := exponentVector a) (b := 0)]

theorem degree_le (cut : AffineCut t K) : cut.polynomial.totalDegree ≤ 1 := by
  unfold polynomial
  refine (totalDegree_add ..).trans (max_le (by simp) (totalDegree_finsetSum_le ?_))
  intro i _
  exact (totalDegree_monomial_le _ _).trans (by simp)

end AffineCut

/-- Base change the integer equations, followed by the affine slice equations. -/
noncomputable def slicedSystem (F : Fin e → MvPolynomial (Fin t) ℤ) (cuts : Fin s → AffineCut t K) :
    Fin (e+s) → MvPolynomial (Fin t) K :=
  Fin.addCases (fun i => map (Int.castRingHom K) (F i)) (fun i => (cuts i).polynomial)

/-- Numerical input for the indexed matrix algorithm after prime reduction. -/
def slicedQueryData (Q d N : ℕ) (read : Fin e → (Fin t → ℕ) → ℤ) (cuts : Fin s → AffineCut t K) :
    QueryData t (e+s) K where
  fieldOrder := Q
  degreeBound := d
  pointBound := N
  getCoeff := Fin.addCases (fun i a => (read i a : K)) (fun i => (cuts i).getCoeff)

theorem slicedQueryData_presents [Fintype K] (F : Fin e → MvPolynomial (Fin t) ℤ) (Q d N : ℕ)
    (read : Fin e → (Fin t → ℕ) → ℤ) (cuts : Fin s → AffineCut t K)
    (hQ : Q = Fintype.card K) (hd : 3 ≤ d) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hread : ∀ i a, read i a = (F i).coeff (exponentVector a)) :
    (slicedQueryData Q d N read cuts).Presents (slicedSystem F cuts) := by
  refine ⟨hQ, hd, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [slicedSystem, Fin.addCases_left]
      exact (Finset.sup_mono (support_map_subset _ _)).trans (hF i)
    · simp only [slicedSystem, Fin.addCases_right]
      exact (cuts i).degree_le.trans (show 1 ≤ d by omega)
  · intro j
    refine Fin.addCases (fun i a => ?_) (fun i a => ?_) j
    · simp only [slicedQueryData, slicedSystem, Fin.addCases_left, hread, coeff_map, Int.coe_castRingHom]
    · simp only [slicedQueryData, slicedSystem, Fin.addCases_right, AffineCut.getCoeff_eq]

end RadicalCertificate.MonomialIndex

end VPVNP
end Computability
end OAI
