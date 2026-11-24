import OAI.Computability.VPVNP.RadicalCertificate
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The bounded coefficient matrix of the finite slice

Appendix D.1 uses rows given by monomial multiples of the slicing equations.
The bounded Rabinowitsch certificate puts the coefficient vector of the required
power of a vanishing polynomial in this matrix's row space. Conversely, row-space
membership implies vanishing at every geometric zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

open MvPolynomial

variable {K : Type*} {t : ℕ} {ι : Type*}

/-- Multi-indices of total degree at most `D` in the original `t` variables. -/
def BoundedMonomial (t D : ℕ) := {a : Fin t →₀ ℕ // a.sum (fun _ e ↦ e) ≤ D}

/-- The exponent of each variable is at most the total degree bound. -/
def BoundedMonomial.encode {t D : ℕ} (a : BoundedMonomial t D) (i : Fin t) : Fin (D + 1) :=
  ⟨a.val i, Nat.lt_succ_of_le (le_trans (by
    by_cases hi : a.val i = 0
    · exact hi ▸ Nat.zero_le _
    · exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finsupp.mem_support_iff.mpr hi)) a.prop)⟩

theorem BoundedMonomial.encode_injective {t D : ℕ} :
    Function.Injective (BoundedMonomial.encode (t := t) (D := D)) := by
  intro a b hab
  exact Subtype.ext <| Finsupp.ext fun i ↦ congrArg Fin.val (congrFun hab i)

instance (t D : ℕ) : Finite (BoundedMonomial t D) :=
  Finite.of_injective _ BoundedMonomial.encode_injective

noncomputable instance (t D : ℕ) : Fintype (BoundedMonomial t D) := Fintype.ofFinite _

/-- Each of the `t` exponents admits at most `D + 1` choices. -/
theorem card_boundedMonomial_le (t D : ℕ) :
    Fintype.card (BoundedMonomial t D) ≤ (D + 1) ^ t := by
  simpa using Fintype.card_le_of_injective (BoundedMonomial.encode (t := t) (D := D))
    BoundedMonomial.encode_injective

section

variable [CommSemiring K]

/-- Coefficient row in the ordered matrix columns through degree `D`. -/
noncomputable def coefficientRow (D : ℕ) :
    MvPolynomial (Fin t) K →ₗ[K] (BoundedMonomial t D → K) :=
  LinearMap.pi fun a ↦ lcoeff K a.val

/-- The row indexed by `(i, a)` is the coefficient vector of `X^a Fᵢ`. -/
noncomputable def macaulayMatrix (F : ι → MvPolynomial (Fin t) K) (L D : ℕ) :
    Matrix (ι × BoundedMonomial t L) (BoundedMonomial t D) K :=
  fun (i, a) ↦ coefficientRow D (monomial a.val 1 * F i)

/-- The coefficient of a monomial multiple is the original coefficient with its
exponent shifted, or zero if one of the exponents is too small. -/
theorem macaulayMatrix_apply (F : ι → MvPolynomial (Fin t) K) {L D : ℕ}
    (r : ι × BoundedMonomial t L) (j : BoundedMonomial t D) :
    macaulayMatrix F L D r j =
      if r.2.val ≤ j.val then (F r.1).coeff (j.val - r.2.val) else 0 := by
  change (monomial r.2.val 1 * F r.1).coeff j.val = _
  simp [coeff_monomial_mul']

/-- For integer equations, the same absolute coefficient bound applies to every row. -/
theorem macaulayMatrix_natAbs_le (F : ι → MvPolynomial (Fin t) ℤ) {L D B : ℕ}
    (hB : ∀ i a, ((F i).coeff a).natAbs ≤ B) (r : ι × BoundedMonomial t L)
    (j : BoundedMonomial t D) : (macaulayMatrix F L D r j).natAbs ≤ B := by
  rw [macaulayMatrix_apply]
  split_ifs <;> simp [hB]

/-- The row augmenting the certificate matrix has a single nonzero coefficient, one. -/
theorem coefficientRow_one_natAbs_le {D : ℕ} (j : BoundedMonomial t D) :
    ((coefficientRow D (1 : MvPolynomial (Fin t) ℤ)) j).natAbs ≤ 1 := by
  change ((1 : MvPolynomial (Fin t) ℤ).coeff j.val).natAbs ≤ 1
  rw [coeff_one]
  split_ifs <;> decide

private noncomputable def polynomialRows (F : ι → MvPolynomial (Fin t) K) (L : ℕ) :
    Submodule K (MvPolynomial (Fin t) K) :=
  Submodule.span K (Set.range (fun p : ι × BoundedMonomial t L ↦ monomial p.2.val 1 * F p.1))

private theorem rowSpan_eq (F : ι → MvPolynomial (Fin t) K) (L D : ℕ) :
    Submodule.span K (Set.range (macaulayMatrix F L D).row) =
      (polynomialRows F L).map (coefficientRow D) := by
  rw [polynomialRows, Submodule.map_span, ← Set.range_comp]
  rfl

private theorem mul_mem_rows (F : ι → MvPolynomial (Fin t) K) {L : ℕ} (i : ι)
    (g : MvPolynomial (Fin t) K) (hg : g.totalDegree ≤ L) : g * F i ∈ polynomialRows F L := by
  have he : g * F i = ∑ a ∈ g.support, g.coeff a • (monomial a 1 * F i) := by
    conv_lhs => rw [g.as_sum, Finset.sum_mul]
    simp only [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
  rw [he]
  exact Submodule.sum_mem _ fun a ha ↦ Submodule.smul_mem _ _ <|
    Submodule.subset_span ⟨(i, ⟨a, (le_totalDegree ha).trans hg⟩), rfl⟩

/-- Bounded multipliers express the coefficient row of a polynomial combination
in the span of the Macaulay rows, over any commutative semiring. -/
theorem coefficientRow_sum_mul_mem [Fintype ι] (F A : ι → MvPolynomial (Fin t) K)
    {L : ℕ} (D : ℕ) (hA : ∀ i, (A i).totalDegree ≤ L) :
    coefficientRow D (∑ i, A i * F i) ∈ Submodule.span K (Set.range (macaulayMatrix F L D).row) := by
  rw [rowSpan_eq]
  exact ⟨_, Submodule.sum_mem _ fun i _ ↦ mul_mem_rows F i _ (hA i), rfl⟩

end

variable [Field K]

/-- The row space test resulting from the bounded inconsistency certificate, with the
paper's multiplier bound `H + P * R₀` and column bound `H + P * R₀ + d`. -/
theorem coefficientRow_pow_mem [Fintype ι] (F : ι → MvPolynomial (Fin t) K)
    {f : MvPolynomial (Fin t) K} (A : ι → MvPolynomial (Fin (t + 1)) K)
    (B : MvPolynomial (Fin (t + 1)) K) {H P R₀ d : ℕ} (hHP : H ≤ P) (hP : P ≠ 0)
    (hA : ∀ i, (A i).totalDegree ≤ H) (hf : f.totalDegree ≤ R₀)
    (hcert : (∑ i, A i * rename Fin.succ (F i)) + B * (1 - X 0 * rename Fin.succ f) = 1) :
    coefficientRow (H + P * R₀ + d) (f ^ P) ∈ Submodule.span K
      (Set.range (macaulayMatrix F (H + P * R₀) (H + P * R₀ + d)).row) := by
  by_cases hz : f = 0
  · simp [hz, zero_pow hP]
  obtain ⟨he, hb⟩ := clear_certificate F hz A B hHP hA hcert
  rw [← he]
  exact coefficientRow_sum_mul_mem F _ _ fun i ↦
    (hb i).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hf) _)

private theorem eq_of_coefficientRow_eq {D : ℕ} {p q : MvPolynomial (Fin t) K}
    (hp : p.totalDegree ≤ D) (hq : q.totalDegree ≤ D)
    (he : coefficientRow D p = coefficientRow D q) : p = q := by
  ext a
  by_cases ha : a.sum (fun _ e ↦ e) ≤ D
  · exact congrFun he ⟨a, ha⟩
  · have hp' : a ∉ p.support := fun h ↦ ha ((le_totalDegree h).trans hp)
    have hq' : a ∉ q.support := fun h ↦ ha ((le_totalDegree h).trans hq)
    simp_all [mem_support_iff]

private theorem rows_degree_le (F : ι → MvPolynomial (Fin t) K) {d L : ℕ}
    (hF : ∀ i, (F i).totalDegree ≤ d) :
    polynomialRows F L ≤ restrictTotalDegree (Fin t) K (L + d) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨i, a⟩, rfl⟩
  apply (mem_restrictTotalDegree ..).mpr
  exact (totalDegree_mul _ _).trans (Nat.add_le_add
    ((totalDegree_monomial_le _ _).trans a.prop) (hF i))

/-- A coefficient row in the Macaulay row space vanishes at all common zeros of the
equations, including zeros in arbitrary extension fields. -/
theorem aeval_eq_zero_of_row_mem {E : Type*} [Field E] [Algebra K E]
    (F : ι → MvPolynomial (Fin t) K) {L d : ℕ} (hF : ∀ i, (F i).totalDegree ≤ d)
    (p : MvPolynomial (Fin t) K) (hp : p.totalDegree ≤ L + d)
    (hrow : coefficientRow (L + d) p ∈ Submodule.span K (Set.range (macaulayMatrix F L (L + d)).row))
    (x : Fin t → E) (hx : ∀ i, aeval x (F i) = 0) : aeval x p = 0 := by
  rw [rowSpan_eq] at hrow
  obtain ⟨q, hq, he⟩ := hrow
  have hdeg := (mem_restrictTotalDegree ..).mp (rows_degree_le F hF hq)
  have heq := eq_of_coefficientRow_eq hdeg hp he
  subst p
  have hker : polynomialRows F L ≤ LinearMap.ker (aeval x).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨i, a⟩, rfl⟩
    change aeval x (monomial a.val 1 * F i) = 0
    simp [hx i]
  exact hker hq

end RadicalCertificate

end VPVNP
end Computability
end OAI
