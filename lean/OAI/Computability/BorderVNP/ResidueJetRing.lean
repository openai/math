import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-! # Truncated parameter coordinates

The quotient by the (d+1)-st powers of the individual variables has a well-defined
coefficient of the top monomial, whose exponents all equal d. Its positive-degree
ideal annihilates that monomial. These facts also hold over rings with nilpotents.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue.JetRing

open MvPolynomial
open scoped Classical

variable (ι B : Type*) [CommRing B] (d : ℕ)

/-- The ideal truncating every individual coordinate after degree d. -/
noncomputable def truncIdeal : Ideal (MvPolynomial ι B) :=
  Ideal.span (Set.range fun i : ι => (X i : MvPolynomial ι B) ^ (d + 1))

/-- The ring of multivariate jets of degree at most d in each coordinate. -/
abbrev Carrier := MvPolynomial ι B ⧸ truncIdeal ι B d

variable {ι B}

/-- The class of a polynomial in the jet ring. -/
noncomputable abbrev mk := Ideal.Quotient.mk (truncIdeal ι B d)

/-- A nilpotent coordinate of the jet ring. -/
noncomputable def coord (i : ι) : Carrier ι B d := mk d (X i)

/-- The defining nilpotence relation. -/
theorem coord_pow (i : ι) : (coord d i : Carrier ι B d) ^ (d+1) = 0 := by
  rw [coord, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- A polynomial represents zero exactly when every monomial has an exponent
strictly greater than d. -/
theorem mem_truncIdeal (f : MvPolynomial ι B) :
    f ∈ truncIdeal ι B d ↔ ∀ m ∈ f.support, ∃ i, d < m i := by
  have h := @mem_ideal_span_monomial_image ι B _ f (Set.range fun i : ι => Finsupp.single i (d+1))
  have hs : ((fun m : ι →₀ ℕ => monomial m (1 : B)) ''
      Set.range (fun i : ι => Finsupp.single i (d+1))) =
      Set.range (fun i : ι => (X i : MvPolynomial ι B) ^ (d+1)) := by
    ext a
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, X_pow_eq_monomial⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, X_pow_eq_monomial.symm⟩
  rw [hs] at h
  rw [truncIdeal, h]
  simp only [Set.mem_range, exists_exists_eq_and, Finsupp.single_le_iff, Nat.succ_le_iff]

variable [Fintype ι]

/-- Coefficient of the top box monomial, descending from the polynomial ring. -/
noncomputable def top : Carrier ι B d →ₗ[B] B :=
  ((truncIdeal ι B d).restrictScalars B).liftQ
    (lcoeff B (Finsupp.equivFunOnFinite.symm fun _ : ι => d)) fun f hf => by
      change f.coeff _ = 0
      by_contra hn
      obtain ⟨i, hi⟩ := (mem_truncIdeal d f).mp hf _ (mem_support_iff.mpr hn)
      exact lt_irrefl d hi

/-- Coefficient on polynomial representatives. -/
theorem top_mk (f : MvPolynomial ι B) :
    top d (mk d f) = f.coeff (Finsupp.equivFunOnFinite.symm fun _ : ι => d) := rfl

private theorem prod_coord_eq_monomial (b : ι → ℕ) :
    (∏ i, coord d i ^ b i : Carrier ι B d) =
      mk d (monomial (Finsupp.equivFunOnFinite.symm b) 1) := by
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow]
  rfl

/-- The value of the top coefficient functional on every coordinate monomial. -/
theorem top_monomial (b : ι → ℕ) :
    top d (∏ i, coord d i ^ b i : Carrier ι B d) = if b = (fun _ => d) then 1 else 0 := by
  rw [prod_coord_eq_monomial, top_mk, coeff_monomial]
  simp

/-- Every polynomial with only terms of degree greater than the top degree is zero in the jet ring. -/
theorem high_degree_vanish {f : MvPolynomial ι B}
    (hf : f ∈ idealOfVars ι B ^ (Fintype.card ι * d + 1)) : mk d f = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_truncIdeal]
  intro m hm
  by_contra! h
  have hl := (mem_pow_idealOfVars_iff _ f).mp hf m hm
  rw [Finsupp.degree_eq_sum] at hl
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
  exact (Nat.not_succ_le_self _) (hl.trans (by simpa using hu))

/-- The top monomial in the jet ring. -/
noncomputable def socle : Carrier ι B d := ∏ i, coord d i ^ d

private theorem socle_rep_mem :
    (∏ i : ι, (X i : MvPolynomial ι B) ^ d) ∈ idealOfVars ι B ^ (Fintype.card ι * d) := by
  rw [prod_X_pow]
  by_cases h : (1 : B) = 0
  · simp [h]
  rw [monomial_mem_pow_idealOfVars_iff _ _ h, Finsupp.degree_eq_sum]
  simp

/-- Only the constant term of a polynomial survives multiplication by the socle. -/
theorem mul_socle (f : MvPolynomial ι B) :
    mk d f * socle (ι := ι) (B := B) d = algebraMap B _ (constantCoeff f) * socle d := by
  have h : f - C (constantCoeff f) ∈ idealOfVars ι B ^ 1 := by
    rw [mem_pow_idealOfVars_iff']
    intro m hm
    have hz : m = 0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
    simp [hz, constantCoeff_eq]
  have ht := Ideal.mul_mem_mul h (socle_rep_mem (ι := ι) (B := B) d)
  rw [← pow_add, Nat.add_comm 1] at ht
  have hv := high_degree_vanish d ht
  rw [map_mul, map_sub, sub_mul, sub_eq_zero] at hv
  change mk d f * (∏ i : ι, mk d (X i : MvPolynomial ι B) ^ d) =
    mk d (C (constantCoeff f)) * (∏ i : ι, mk d (X i : MvPolynomial ι B) ^ d)
  simpa only [map_prod, map_pow] using hv

end Residue.JetRing

end BorderVNP
end Computability
end OAI
