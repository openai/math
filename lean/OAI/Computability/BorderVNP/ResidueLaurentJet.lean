import OAI.Computability.BorderVNP.ResidueLaurent

/-! # Frobenius coordinates and truncated Taylor evaluation

Grouping all integer exponents modulo q = pᵘ gives a basis of κ((s)) over
its q-th powers. The truncated Taylor evaluation sends s to s + δ and keeps
all q-th powers fixed, for δᵠ = 0. This includes series with poles at s = 0.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open HahnSeries
open scoped LaurentSeries

variable {K : Type*} [Field K] (p u : ℕ) [ExpChar K p] [PerfectRing K p]

/-- The Laurent uniformizer s. -/
noncomputable def parameter (K : Type*) [Field K] : LaurentSeries K := single 1 1

private theorem parameter_pow (r : ℕ) : parameter K ^ r = single (r : ℤ) 1 := by
  simp [parameter, single_pow]

/-- The q-th roots of the coefficients in a fixed exponent class r modulo q. -/
noncomputable def sectionSeries (r : ℕ) (D : LaurentSeries K) : LaurentSeries K :=
  cartier p u (single (((p ^ u : ℕ) : ℤ) - 1 - r) 1 * D)

/-- Laurent coefficient formula for a Frobenius coordinate. -/
theorem sectionSeries_coeff (r : ℕ) (D : LaurentSeries K) (k : ℤ) :
    (sectionSeries p u r D).coeff k =
      (iterateFrobeniusEquiv K p u).symm (D.coeff ((p ^ u : ℕ) * k + r)) := by
  rw [sectionSeries, cartier_coeff, coeff_single_mul, one_mul]
  congr 2
  ring

private theorem sectionSeries_add (r : ℕ) (D E : LaurentSeries K) :
    sectionSeries p u r (D + E) = sectionSeries p u r D + sectionSeries p u r E := by
  ext k
  simp only [sectionSeries_coeff, coeff_add, map_add]

private theorem sectionSeries_zero (r : ℕ) : sectionSeries p u r (0 : LaurentSeries K) = 0 := by
  ext k
  simp only [sectionSeries_coeff, coeff_zero, map_zero]

omit [ExpChar K p] [PerfectRing K p] in
private theorem section_term_coeff (r : ℕ) (U : LaurentSeries K) (k : ℤ) :
    (parameter K ^ r * U ^ p ^ u).coeff k = (U ^ p ^ u).coeff (k - r) := by
  rw [parameter_pow, coeff_single_mul, one_mul]

omit [PerfectRing K p] in
private theorem section_term_other (r : ℕ) (U : LaurentSeries K) (k : ℤ)
    (hr : r < p ^ u) (hk : k % (p ^ u : ℕ) ≠ r) :
    (parameter K ^ r * U ^ p ^ u).coeff k = 0 := by
  rw [section_term_coeff]
  apply coeff_pow_frobenius_of_not_dvd
  rintro ⟨a, ha⟩
  apply hk
  rw [show k = r + (p ^ u : ℕ) * a by omega, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hr)]

/-- Unique reconstruction of a Laurent series from all its q Frobenius coordinates. -/
theorem sum_sections (D : LaurentSeries K) :
    ∑ r ∈ Finset.range (p ^ u), parameter K ^ r * sectionSeries p u r D ^ p ^ u = D := by
  ext k
  let q : ℤ := (p ^ u : ℕ)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast expChar_pow_pos K p u
  let r := (k % q).toNat
  have hr : (r : ℤ) = k % q := Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne')
  have hr' : r < p ^ u := by
    exact_mod_cast (show (r : ℤ) < ((p ^ u : ℕ) : ℤ) from hr.trans_lt (Int.emod_lt_of_pos _ hq))
  rw [coeff_sum, Finset.sum_eq_single_of_mem r (Finset.mem_range.mpr hr')]
  · rw [section_term_coeff, hr]
    have hkr : q * (k / q) + k % q = k := Int.mul_ediv_add_emod k q
    rw [show k - k % q = q * (k / q) by omega, coeff_pow_frobenius_mul, sectionSeries_coeff,
      hr, hkr]
    exact (iterateFrobeniusEquiv K p u).apply_symm_apply _
  · intro b hb hbr
    apply section_term_other p u b _ k (Finset.mem_range.mp hb)
    rw [← hr]
    exact_mod_cast hbr.symm

private theorem section_coordinate (r i : ℕ) (hr : r < p ^ u) (hi : i < p ^ u)
    (U : LaurentSeries K) :
    sectionSeries p u i (parameter K ^ r * U ^ p ^ u) = if i = r then U else 0 := by
  ext k
  rw [sectionSeries_coeff]
  by_cases h : i = r
  · subst i
    rw [ite_eq_left rfl, section_term_coeff, add_sub_cancel_right, coeff_pow_frobenius_mul]
    exact (iterateFrobeniusEquiv K p u).symm_apply_apply _
  · rw [ite_eq_right h, section_term_other p u r U _ hr, map_zero, coeff_zero]
    rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by exact_mod_cast hi)]
    exact_mod_cast h

/-- The last Frobenius coordinate is exactly the Cartier operator on differentials. -/
theorem section_last (D : LaurentSeries K) :
    sectionSeries p u (p ^ u - 1) D = cartier p u D := by
  ext k
  rw [sectionSeries_coeff, cartier_coeff, Nat.cast_sub (expChar_pow_pos K p u), Nat.cast_one]
  congr 2
  ring


variable {R : Type*} [CommRing R]

/-- Evaluation of the Frobenius expansion at v in a coefficient algebra. -/
noncomputable def jetAdd (f : LaurentSeries K →+* R) (v : R) : LaurentSeries K →+ R where
  toFun D := ∑ r ∈ Finset.range (p ^ u), v ^ r * f (sectionSeries p u r D ^ p ^ u)
  map_zero' := by simp [sectionSeries_zero, zero_pow (expChar_pow_pos K p u).ne']
  map_add' D E := by
    have : ExpChar (LaurentSeries K) p :=
      expChar_of_injective_ringHom (f := HahnSeries.C) HahnSeries.C_injective p
    simp only [sectionSeries_add, add_pow_expChar_pow, map_add, mul_add, Finset.sum_add_distrib]

private theorem jetAdd_term (f : LaurentSeries K →+* R) (v : R)
    (r : ℕ) (hr : r < p ^ u) (U : LaurentSeries K) :
    jetAdd p u f v (parameter K ^ r * U ^ p ^ u) = v ^ r * f (U ^ p ^ u) := by
  change ∑ i ∈ Finset.range _, _ = _
  rw [Finset.sum_eq_single_of_mem r (Finset.mem_range.mpr hr)]
  · rw [section_coordinate p u r r hr hr, ite_eq_left rfl]
  · intro i hi hir
    rw [section_coordinate p u r i hr (Finset.mem_range.mp hi), ite_eq_right hir,
      zero_pow (expChar_pow_pos K p u).ne', map_zero, mul_zero]

private theorem jetAdd_term_any (f : LaurentSeries K →+* R) (v : R)
    (hv : v ^ p ^ u = f (parameter K ^ p ^ u)) (r : ℕ) (U : LaurentSeries K) :
    jetAdd p u f v (parameter K ^ r * U ^ p ^ u) = v ^ r * f (U ^ p ^ u) := by
  let q := p ^ u
  let a := r / q
  let b := r % q
  have hr : b + q * a = r := Nat.mod_add_div _ _
  have hrem : b < q := Nat.mod_lt _ (expChar_pow_pos K p u)
  have rewriteTerm : parameter K ^ r * U ^ q =
      parameter K ^ b * (parameter K ^ a * U) ^ q := by
    rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mul_comm a q, hr]
  rw [rewriteTerm, jetAdd_term p u f v b hrem, mul_pow, map_mul, ← mul_assoc, ← pow_mul,
    Nat.mul_comm a q, pow_mul, map_pow, ← hv, ← pow_mul, ← pow_add, hr]

/-- Frobenius coordinates define a ring homomorphism whenever the new parameter has
the same q-th power as the original one. -/
noncomputable def jetHom (f : LaurentSeries K →+* R) (v : R)
    (hv : v ^ p ^ u = f (parameter K ^ p ^ u)) : LaurentSeries K →+* R where
  __ := jetAdd p u f v
  map_one' := by
    change jetAdd p u f v 1 = 1
    simpa only [pow_zero, one_mul, one_pow, map_one] using
      jetAdd_term p u f v 0 (expChar_pow_pos K p u) 1
  map_mul' D E := by
    change jetAdd p u f v (D * E) = jetAdd p u f v D * jetAdd p u f v E
    let q := p ^ u
    let term (i : ℕ) (U : LaurentSeries K) := parameter K ^ i * U ^ q
    have hterm (i j : ℕ) (U V : LaurentSeries K) :
        jetAdd p u f v (term i U * term j V) =
          jetAdd p u f v (term i U) * jetAdd p u f v (term j V) := by
      change jetAdd p u f v (parameter K ^ i * U ^ q * (parameter K ^ j * V ^ q)) = _
      rw [mul_mul_mul_comm, ← pow_add, ← mul_pow, jetAdd_term_any p u f v hv]
      change v ^ (i + j) * f ((U * V) ^ q) =
        jetAdd p u f v (parameter K ^ i * U ^ q) * jetAdd p u f v (parameter K ^ j * V ^ q)
      rw [jetAdd_term_any p u f v hv, jetAdd_term_any p u f v hv, pow_add, mul_pow,
        map_mul, mul_mul_mul_comm]
    conv => lhs; rw [← sum_sections p u D, ← sum_sections p u E]
    conv => rhs; rw [← sum_sections p u D, ← sum_sections p u E]
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm j i _ _

/-- On a monomial times a q-th power, the jet substitutes v for s and leaves the
q-th power in the coefficient ring. -/
theorem jetHom_term (f : LaurentSeries K →+* R) (v : R)
    (hv : v ^ p ^ u = f (parameter K ^ p ^ u)) (r : ℕ) (U : LaurentSeries K) :
    jetHom p u f v hv (parameter K ^ r * U ^ p ^ u) = v ^ r * f (U ^ p ^ u) :=
  jetAdd_term_any p u f v hv r U

/-- Evaluating s + δ for a nilpotent infinitesimal δ of order at most q. -/
noncomputable def taylorJet [ExpChar R p] (f : LaurentSeries K →+* R) (δ : R)
    (hδ : δ ^ p ^ u = 0) : LaurentSeries K →+* R :=
  jetHom p u f (f (parameter K) + δ) <| by rw [add_pow_expChar_pow, hδ, add_zero, map_pow]


/-- Polynomial of degree less than q representing the truncated Taylor expansion. -/
noncomputable def jetPolynomial (D : LaurentSeries K) : Polynomial (LaurentSeries K) :=
  ∑ r ∈ Finset.range (p ^ u),
    Polynomial.C (sectionSeries p u r D ^ p ^ u) * (Polynomial.X + Polynomial.C (parameter K)) ^ r

/-- The Taylor representative of a single Frobenius-basis term. -/
theorem jetPolynomial_term (r : ℕ) (hr : r < p ^ u) (U : LaurentSeries K) :
    jetPolynomial p u (parameter K ^ r * U ^ p ^ u) =
      Polynomial.C (U ^ p ^ u) * (Polynomial.X + Polynomial.C (parameter K)) ^ r := by
  rw [jetPolynomial, Finset.sum_eq_single_of_mem r (Finset.mem_range.mpr hr)]
  · rw [section_coordinate p u r r hr hr, ite_eq_left rfl]
  · intro i hi hir
    rw [section_coordinate p u r i hr (Finset.mem_range.mp hi), ite_eq_right hir,
      zero_pow (expChar_pow_pos K p u).ne', map_zero, zero_mul]

/-- Evaluating the representative at a nilpotent element gives the Taylor homomorphism. -/
theorem eval_jetPolynomial [ExpChar R p] (f : LaurentSeries K →+* R) (δ : R)
    (hδ : δ ^ p ^ u = 0) (D : LaurentSeries K) :
    (jetPolynomial p u D).eval₂ f δ = taylorJet p u f δ hδ D := by
  change (jetPolynomial p u D).eval₂ f δ =
    ∑ r ∈ Finset.range (p ^ u), (f (parameter K) + δ) ^ r * f (sectionSeries p u r D ^ p ^ u)
  simp only [jetPolynomial, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm, mul_comm]

/-- The coefficient of the last surviving Taylor term, u^(q−1), is the q-th power
of the Laurent coefficient series of the Cartier differential. -/
theorem jetPolynomial_top_coeff (D : LaurentSeries K) :
    (jetPolynomial p u D).coeff (p ^ u - 1) = cartier p u D ^ p ^ u := by
  classical
  have hq := expChar_pow_pos K p u
  rw [jetPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem (p ^ u - 1) (Finset.mem_range.mpr (by omega))]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, section_last]
    simp
  · intro i hi hne
    have hlt : i < p ^ u - 1 := by have := Finset.mem_range.mp hi; omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt hlt]
    simp

end Residue

end BorderVNP
end Computability
end OAI
