import OAI.Computability.BorderVNP.ResidueJetRing

/-! # Discarding higher-order terms in the top coordinate product

In an h-dimensional box of truncation order d+1, every product of h coordinate
equations to the d-th power is determined by their linear terms when their constant
terms vanish. The proof tracks powers of the ideal of variables before quotienting.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue.JetRing

open MvPolynomial
open scoped Classical

variable {ι B : Type*} [CommRing B] [Fintype ι]

/-- The degree-one part of an equation in the jet coordinates. -/
noncomputable def linearPart (f : MvPolynomial ι B) : MvPolynomial ι B :=
  ∑ i : ι, C (f.coeff (Finsupp.single i 1)) * X i

/-- Evaluating the linear part in the jet ring uses the linear coefficients as its row. -/
theorem mk_linearPart (d : ℕ) (f : MvPolynomial ι B) :
    mk d (linearPart f) = ∑ i, algebraMap B (Carrier ι B d) (f.coeff (Finsupp.single i 1)) *
      coord d i := by
  simp only [linearPart, map_sum, map_mul]
  rfl

private theorem linearPart_coeff (f : MvPolynomial ι B) (j : ι) :
    (linearPart f).coeff (Finsupp.single j 1) = f.coeff (Finsupp.single j 1) := by
  rw [linearPart, coeff_sum, Finset.sum_eq_single j]
  · simp [coeff_C_mul, coeff_X]
  · intro i _ hij
    rw [coeff_C_mul, coeff_X, ite_eq_right, mul_zero]
    intro hs
    have hh := DFunLike.congr_fun hs i
    simp [hij.symm] at hh
  · simp

private theorem linearPart_constant (f : MvPolynomial ι B) : constantCoeff (linearPart f) = 0 := by
  simp [linearPart, map_sum]

omit [Fintype ι] in
private theorem mem_variableIdeal_of_constant_zero (f : MvPolynomial ι B) (hf : constantCoeff f = 0) :
    f ∈ idealOfVars ι B := by
  rw [← pow_one (idealOfVars ι B), mem_pow_idealOfVars_iff']
  intro m hm
  have hz := (Finsupp.degree_eq_zero_iff m).mp (show Finsupp.degree m = 0 by omega)
  simpa only [hz, ← constantCoeff_eq] using hf

private theorem quadratic_error (f : MvPolynomial ι B) (hf : constantCoeff f = 0) :
    f - linearPart f ∈ idealOfVars ι B ^ 2 := by
  rw [mem_pow_idealOfVars_iff']
  intro m hm
  rcases eq_or_ne (Finsupp.degree m) 0 with h0 | hne
  · have hz := (Finsupp.degree_eq_zero_iff m).mp h0
    simp only [hz, ← constantCoeff_eq, map_sub, hf, linearPart_constant, sub_zero]
  · have hone : m.sum (fun _ n => n) = 1 := show Finsupp.degree m = 1 by omega
    obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff m).mp hone
    rw [coeff_sub, linearPart_coeff, sub_self]

private theorem pow_error {R : Type*} [CommRing R] {I : Ideal R} {a b : R}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a-b ∈ I ^ 2) (d : ℕ) :
    a ^ d - b ^ d ∈ I ^ (d+1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ a, pow_succ b, show a ^ d * a - b ^ d * b =
      (a ^ d - b ^ d) * a + b ^ d * (a - b) by ring]
    apply Ideal.add_mem
    · simpa only [pow_succ] using Ideal.mul_mem_mul ih ha
    · simpa only [← pow_add] using Ideal.mul_mem_mul (Ideal.pow_mem_pow hb d) hab

omit [Fintype ι] in
private theorem product_error {R : Type*} [CommRing R] {I : Ideal R} (d : ℕ)
    (a b : ι → R) (ha : ∀ i, a i ∈ I) (hb : ∀ i, b i ∈ I)
    (hab : ∀ i, a i-b i ∈ I ^ 2) (s : Finset ι) :
    (∏ i ∈ s, a i ^ d) - (∏ i ∈ s, b i ^ d) ∈ I ^ (s.card * d + 1) := by
  have prod_mem (g : ι → R) (hg : ∀ i, g i ∈ I) (t : Finset ι) :
      (∏ i ∈ t, g i ^ d) ∈ I ^ (t.card * d) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul,
        Nat.add_comm, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hg i) _) ih
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    set A := ∏ j ∈ s, a j ^ d
    set B := ∏ j ∈ s, b j ^ d
    rw [show a i ^ d * A - b i ^ d * B = (a i ^ d - b i ^ d) * A + b i ^ d * (A-B) by ring]
    apply Ideal.add_mem
    · have h := Ideal.mul_mem_mul (pow_error (ha i) (hb i) (hab i) d) (prod_mem a ha s)
      rwa [← pow_add, show (d + 1) + s.card * d = (s.card + 1) * d + 1 by ring] at h
    · have h := Ideal.mul_mem_mul (Ideal.pow_mem_pow (hb i) d) ih
      rwa [← pow_add, show d + (s.card * d + 1) = (s.card + 1) * d + 1 by ring] at h

/-- The product of the full equations to power d agrees in the truncated box with
the product of their degree-one parts. -/
theorem prod_pow_eq_linear (d : ℕ) (g : ι → MvPolynomial ι B)
    (hg : ∀ i, constantCoeff (g i) = 0) :
    ∏ i, mk d (g i) ^ d = ∏ i, mk d (linearPart (g i)) ^ d := by
  have h := product_error d g (fun i => linearPart (g i))
    (fun i => mem_variableIdeal_of_constant_zero (g i) (hg i))
    (fun i => mem_variableIdeal_of_constant_zero _ (linearPart_constant (g i)))
    (fun i => quadratic_error (g i) (hg i)) Finset.univ
  rw [Finset.card_univ] at h
  have hz := high_degree_vanish d h
  rw [map_sub, sub_eq_zero, map_prod, map_prod] at hz
  simpa only [map_pow] using hz

end Residue.JetRing

end BorderVNP
end Computability
end OAI
