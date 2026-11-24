import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Clearing the Rabinowitsch certificate

In Appendix D.1 of *VP and VNP differ over every field*, the auxiliary equation
`1 - y f` converts a vanishing question into a certificate of inconsistency.
Index the original variables by `Fin t` and the extra variable by zero in
`Fin (t + 1)`. Substitution of `1/f` in the fraction field clears all denominators
with a single power `f ^ P` and controls the total degree of each new multiplier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

open MvPolynomial
open scoped Polynomial

variable {K : Type*} [Field K] {t : ℕ}

private theorem univariate_rename_succ (p : MvPolynomial (Fin t) K) :
    finSuccEquiv K t (rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, finSuccEquiv_X_succ]

/-- The coefficient of `y ^ b` is multiplied by `f ^ (P - b)` to clear its denominator. -/
noncomputable def clearedMultiplier (P : ℕ) (f : MvPolynomial (Fin t) K)
    (A : MvPolynomial (Fin (t + 1)) K) : MvPolynomial (Fin t) K :=
  let a := finSuccEquiv K t A
  ∑ b ∈ a.support, a.coeff b * f ^ (P - b)

/-- Total-degree control for the multipliers indexing the rows of the Macaulay matrix. -/
theorem clearedMultiplier_totalDegree (P : ℕ) (f : MvPolynomial (Fin t) K)
    (A : MvPolynomial (Fin (t + 1)) K) :
    (clearedMultiplier P f A).totalDegree ≤ A.totalDegree + P * f.totalDegree := by
  apply totalDegree_finsetSum_le
  intro b hb
  have h := totalDegree_coeff_finSuccEquiv_add_le A b (Polynomial.mem_support_iff.mp hb)
  apply (totalDegree_mul _ _).trans
  exact Nat.add_le_add (by omega) ((totalDegree_pow _ _).trans
    (Nat.mul_le_mul_right _ (Nat.sub_le P b)))

private theorem map_clearedMultiplier (P : ℕ) {f : MvPolynomial (Fin t) K} (hf : f ≠ 0)
    (A : MvPolynomial (Fin (t + 1)) K) (hA : A.totalDegree ≤ P) :
    let φ := algebraMap (MvPolynomial (Fin t) K) (FractionRing (MvPolynomial (Fin t) K))
    φ (clearedMultiplier P f A) =
      (φ f) ^ P * (finSuccEquiv K t A).eval₂ φ (φ f)⁻¹ := by
  intro φ
  have hφ : φ f ≠ 0 := by
    exact fun h ↦ hf (IsFractionRing.injective _ _ (h.trans φ.map_zero.symm))
  rw [clearedMultiplier, map_sum, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have h := totalDegree_coeff_finSuccEquiv_add_le A b (Polynomial.mem_support_iff.mp hb)
  rw [map_mul, map_pow, pow_sub₀ _ hφ (by omega), inv_pow, mul_left_comm]

/-- Bounded Rabinowitsch denominator clearing. From the identity for `1` in the extended
ring, obtain an identity for `f ^ P` in the original polynomial ring. -/
theorem clear_certificate {ι : Type*} [Fintype ι] (F : ι → MvPolynomial (Fin t) K)
    {f : MvPolynomial (Fin t) K} (hf : f ≠ 0) (A : ι → MvPolynomial (Fin (t + 1)) K)
    (B : MvPolynomial (Fin (t + 1)) K) {H P : ℕ} (hHP : H ≤ P)
    (hA : ∀ i, (A i).totalDegree ≤ H)
    (hcert : (∑ i, A i * rename Fin.succ (F i)) + B * (1 - X 0 * rename Fin.succ f) = 1) :
    (∑ i, clearedMultiplier P f (A i) * F i = f ^ P) ∧
      ∀ i, (clearedMultiplier P f (A i)).totalDegree ≤ H + P * f.totalDegree := by
  constructor
  · let φ := algebraMap (MvPolynomial (Fin t) K) (FractionRing (MvPolynomial (Fin t) K))
    have hφ : φ f ≠ 0 := fun h ↦ hf (IsFractionRing.injective _ _ (h.trans φ.map_zero.symm))
    let ψ := Polynomial.eval₂RingHom φ (φ f)⁻¹
    have h := congrArg (fun p ↦ ψ (finSuccEquiv K t p)) hcert
    simp only [map_add, map_sum, map_mul, map_sub, map_one, univariate_rename_succ,
      finSuccEquiv_X_zero] at h
    simp only [ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
      inv_mul_cancel₀ hφ, sub_self, mul_zero, add_zero] at h
    apply IsFractionRing.injective (MvPolynomial (Fin t) K) (FractionRing (MvPolynomial (Fin t) K))
    change φ _ = φ _
    rw [map_sum, map_pow]
    calc
      _ = ∑ i, φ f ^ P * ((finSuccEquiv K t (A i)).eval₂ φ (φ f)⁻¹ * φ (F i)) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_mul]
        have hi := map_clearedMultiplier P hf (A i) ((hA i).trans hHP)
        change φ (clearedMultiplier P f (A i)) = _ at hi
        rw [hi, mul_assoc]
      _ = φ f ^ P := by rw [← Finset.mul_sum, h, mul_one]
  · intro i
    exact (clearedMultiplier_totalDegree _ _ _).trans (Nat.add_le_add_right (hA i) _)

/-- The certificate witnesses membership in the radical of the ideal of the original equations. -/
theorem mem_radical_of_certificate {ι : Type*} [Fintype ι] (F : ι → MvPolynomial (Fin t) K)
    {f : MvPolynomial (Fin t) K} (A : ι → MvPolynomial (Fin (t + 1)) K)
    (B : MvPolynomial (Fin (t + 1)) K) {H P : ℕ} (hHP : H ≤ P)
    (hA : ∀ i, (A i).totalDegree ≤ H)
    (hcert : (∑ i, A i * rename Fin.succ (F i)) + B * (1 - X 0 * rename Fin.succ f) = 1) :
    f ∈ (Ideal.span (Set.range F)).radical := by
  by_cases hf : f = 0
  · exact hf ▸ Ideal.zero_mem _
  · exact Ideal.mem_radical_iff.mpr ⟨P, Ideal.mem_span_range_iff_exists_fun.mpr
      ⟨fun i ↦ clearedMultiplier P f (A i), (clear_certificate F hf A B hHP hA hcert).1⟩⟩

end RadicalCertificate

end VPVNP
end Computability
end OAI
