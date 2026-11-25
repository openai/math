import OAI.Computability.BorderVNP.BranchSpecializationRelations
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log

/-!
# Size of the coefficient matrix in characteristic-zero specialization

For Lemma 9.1 the number of columns may be enormous. The number of parameter
monomials and the coefficient height of each substituted monomial control the
maximal minor, independently of the number of columns.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace BranchSpecialization

open MvPolynomial

variable {σ ι : Type*}

/-- Sum of the absolute values of all integer coefficients. -/
noncomputable def coefficientNorm (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ a ∈ p.support, (p.coeff a).natAbs

/-- Compatibility with the integer coefficient sum in the universal parse table. -/
theorem intCast_coefficientNorm (p : MvPolynomial σ ℤ) :
    (coefficientNorm p : ℤ) = ∑ a ∈ p.support, |p.coeff a| := by
  simp [coefficientNorm]

private theorem partial_norm_le (s : Finset (σ →₀ ℕ)) (p : MvPolynomial σ ℤ) :
    ∑ a ∈ s, (p.coeff a).natAbs ≤ coefficientNorm p := by
  classical
  calc
    _ = ∑ a ∈ s ∩ p.support, (p.coeff a).natAbs := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro a ha hn
      have h : a ∉ p.support := fun hs => hn (Finset.mem_inter.mpr ⟨ha, hs⟩)
      simp [notMem_support_iff.mp h]
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.inter_subset_right)

/-- Each coefficient is bounded by the coefficient norm, including exponents
outside the support. -/
theorem natAbs_coeff_le_norm (p : MvPolynomial σ ℤ) (a : σ →₀ ℕ) :
    (p.coeff a).natAbs ≤ coefficientNorm p := by
  classical
  simpa only [Finset.sum_singleton] using partial_norm_le {a} p

private theorem norm_sum_le {α : Type*} (s : Finset α) (f : α → MvPolynomial σ ℤ) :
    coefficientNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coefficientNorm (f i) := by
  let t := (∑ i ∈ s, f i).support
  calc
    coefficientNorm (∑ i ∈ s, f i) = ∑ a ∈ t, (∑ i ∈ s, (f i).coeff a).natAbs := by
      simp only [coefficientNorm, t, coeff_sum]
    _ ≤ ∑ a ∈ t, ∑ i ∈ s, ((f i).coeff a).natAbs :=
      Finset.sum_le_sum fun _ _ => Int.natAbs_sum_le _ _
    _ = ∑ i ∈ s, ∑ a ∈ t, ((f i).coeff a).natAbs := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun _ _ => partial_norm_le _ _

private theorem norm_monomial (a : σ →₀ ℕ) (z : ℤ) :
    coefficientNorm (monomial a z) = z.natAbs := by
  classical
  by_cases h : z = 0 <;> simp [coefficientNorm, support_monomial, coeff_monomial, h]

/-- Submultiplicativity of the integral coefficient norm. Each pair of source
monomials contributes at most its product of absolute coefficients. -/
theorem coefficientNorm_mul_le (p q : MvPolynomial σ ℤ) :
    coefficientNorm (p * q) ≤ coefficientNorm p * coefficientNorm q := by
  classical
  have hex : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      monomial (a + b) (p.coeff a * q.coeff b) := by
    conv_lhs => rw [p.as_sum, q.as_sum]
    simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
    exact Finset.sum_comm
  rw [hex]
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ a ∈ p.support, ∑ b ∈ q.support,
        coefficientNorm (monomial (a + b) (p.coeff a * q.coeff b)) :=
      Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ = _ := by
      simp only [norm_monomial, Int.natAbs_mul]
      simp only [coefficientNorm, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

private theorem norm_one : coefficientNorm (1 : MvPolynomial σ ℤ) = 1 :=
  norm_monomial (0 : σ →₀ ℕ) 1

private theorem norm_pow_le (p : MvPolynomial σ ℤ) (e : ℕ) :
    coefficientNorm (p ^ e) ≤ coefficientNorm p ^ e := by
  induction e with
  | zero => simp [norm_one]
  | succ e ih =>
    rw [pow_succ, pow_succ]
    exact (coefficientNorm_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

private theorem norm_prod_le {α : Type*} (s : Finset α) (f : α → MvPolynomial σ ℤ) :
    coefficientNorm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coefficientNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [norm_one]
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (coefficientNorm_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

/-- An entry of the substitution matrix needs at most the degree bound times
the number of bits bounding the coefficient norm of a coordinate. -/
theorem relationMatrix_entry_bound (Y : ι → MvPolynomial σ ℤ) (d D b : ℕ)
    (hY : ∀ i, coefficientNorm (Y i) ≤ 2 ^ b)
    (a : BoundedMonomial σ (d * D)) (u : BoundedMonomial ι D) :
    ((relationMatrix Y d D) a u).natAbs ≤ 2 ^ (b * D) := by
  calc
    _ ≤ _ := natAbs_coeff_le_norm _ _
    _ ≤ _ := norm_prod_le u.val.support _
    _ ≤ ∏ i ∈ u.val.support, (2 ^ b) ^ u.val i :=
      Finset.prod_le_prod fun i _ =>
        (norm_pow_le _ _).trans (Nat.pow_le_pow_left (hY i) _)
    _ = 2 ^ (b * u.val.degree) := by
      rw [pow_mul, Finsupp.degree_apply, Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b u.property)

/-- Exact count by grouping exponent vectors by total degree and applying
stars and bars in each degree. -/
theorem card_boundedMonomial (σ : Type*) [Fintype σ] (D : ℕ) :
    Fintype.card (BoundedMonomial σ D) = (D + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  let deg (a : BoundedMonomial σ D) : Fin (D + 1) := ⟨a.val.degree, Nat.lt_succ_of_le a.property⟩
  have fiber (i : Fin (D + 1)) :
      Fintype.card {a : BoundedMonomial σ D // deg a = i} =
        (Fintype.card σ).multichoose i.val := by
    let eqv : {a : BoundedMonomial σ D // deg a = i} ≃
        ((Finset.univ : Finset σ).finsuppAntidiag i.val) :=
      { toFun := fun a => ⟨a.val.val, Finset.mem_finsuppAntidiag.mpr
          ⟨(Finsupp.degree_eq_sum _).symm.trans (congrArg Fin.val a.property), Finset.subset_univ _⟩⟩
        invFun := fun a => by
          have hd : a.val.degree = i.val :=
            (Finsupp.degree_eq_sum _).trans (Finset.mem_finsuppAntidiag.mp a.property).1
          exact ⟨⟨a.val, hd.le.trans (Nat.le_of_lt_succ i.isLt)⟩, Fin.ext hd⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa only [Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ]
      using Fintype.card_congr eqv
  calc
    _ = ∑ i, Fintype.card {a : BoundedMonomial σ D // deg a = i} := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv deg).symm
    _ = ∑ i : Fin (D + 1), (Fintype.card σ).multichoose i.val :=
      Finset.sum_congr rfl fun i _ => fiber i
    _ = _ := by rw [Fin.sum_univ_eq_sum_range ((Fintype.card σ).multichoose), Nat.sum_range_multichoose]

/-- The row index injects into the box of exponents in `0,…,D`. -/
theorem card_boundedMonomial_le (σ : Type*) [Fintype σ] (D : ℕ) :
    Fintype.card (BoundedMonomial σ D) ≤ (D + 1) ^ Fintype.card σ := by
  classical
  let f (a : BoundedMonomial σ D) (i : σ) : Fin (D + 1) :=
    ⟨a.val i, Nat.lt_succ_of_le ((Finsupp.le_degree i a.val).trans a.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun hab i)
  simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- A single-exponential bound for the number of rows, with an explicit binary
exponent. The target coordinate count does not enter this estimate. -/
theorem relationMatrix_row_bound (σ : Type*) [Fintype σ] (d D : ℕ) :
    Fintype.card (BoundedMonomial σ (d * D)) ≤
      2 ^ (Nat.clog 2 (d * D + 1) * Fintype.card σ) := by
  rw [pow_mul]
  exact (card_boundedMonomial_le _ _).trans
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _)

end BranchSpecialization

end BorderVNP
end Computability
end OAI
