import OAI.Computability.VPVNP.ParseCoefficients
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Splitting a coefficient over a cut of the parties

In §4 of *VP and VNP differ over every field*, a homogeneous product contributes
to the coefficient tensor through a sum of products across party cuts. Choosing one
variable at each party makes the queried monomial squarefree. The degree of the first
factor fixes the size of the first side of the cut.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {I J R : Type*}

/-- Exponent vector selecting the variable `(i, a i)` for each party `i ∈ S`. -/
noncomputable def partyExponent (S : Finset I) (a : I → J) : (I × J) →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single (i, a i) 1

/-- An exponent on one side of the cut depends only on assignments on that side. -/
theorem partyExponent_congr (S : Finset I) {a b : I → J} (h : ∀ i ∈ S, a i = b i) :
    partyExponent S a = partyExponent S b := by
  exact Finset.sum_congr rfl fun i hi ↦ by rw [h i hi]

@[simp] theorem degree_partyExponent (S : Finset I) (a : I → J) :
    (partyExponent S a).degree = S.card := by
  simp [partyExponent, Finsupp.degree_single]

variable [CommSemiring R] [Fintype I] [DecidableEq I]

/-- Coefficient of a product on all parties, expressed as a sum over cuts of the
parties themselves. Each term uses the assignments on its respective sides. -/
theorem coeff_mul_partyExponent (f g : MvPolynomial (I × J) R) (a : I → J) :
    (f * g).coeff (partyExponent Finset.univ a) =
      ∑ S : Finset I, f.coeff (partyExponent S a) * g.coeff (partyExponent Sᶜ a) := by
  classical
  let e : I ↪ I × J := ⟨fun i ↦ (i, a i), fun _ _ h ↦ congrArg Prod.fst h⟩
  have hdeg (S : Finset I) : partyExponent S a = squarefreeDegree (S.map e) := by
    simp only [partyExponent, squarefreeDegree, Finset.sum_map]
    rfl
  have hsets : (Finset.univ.map e).powerset = Finset.univ.image (Finset.map e) := by
    simp [Finset.map_eq_image, Finset.powerset_image]
    congr 1
    funext S
    exact (Finset.map_eq_image e S).symm
  rw [hdeg, coeff_mul_squarefree, hsets, Finset.sum_image]
  · refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [← Finset.map_sdiff, ← hdeg, ← hdeg]
    rfl
  · exact fun _ _ _ _ h ↦ Finset.map_injective e h

/-- If the first factor is homogeneous of degree `d`, only cuts of size `d`
contribute. The product for each such cut is separated across its two sides. -/
theorem coeff_mul_partyExponent_homogeneous (f g : MvPolynomial (I × J) R) {d : ℕ}
    (hf : f.IsHomogeneous d) (a : I → J) :
    (f * g).coeff (partyExponent Finset.univ a) =
      ∑ S : Finset I with S.card = d,
        f.coeff (partyExponent S a) * g.coeff (partyExponent Sᶜ a) := by
  classical
  rw [coeff_mul_partyExponent, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  by_cases hS : S.card = d
  · simp [hS]
  · have hz : f.coeff (partyExponent S a) = 0 := by
      apply IsWeightedHomogeneous.coeff_eq_zero hf
      change Finsupp.weight (fun _ ↦ 1) (partyExponent S a) ≠ d
      rwa [← Finsupp.degree_eq_weight_one, degree_partyExponent]
    simp [hS, hz]

end VPVNP
end Computability
end OAI
