import Lemmata.FockCircuits.SignedKernel

/-!
# Shifted fermionic residues

Appendix B, equation (B.1), of *VP and VNP differ over every field* extracts a
different coefficient for every shift. Khoruzhii's `weighted_matrix_residue`
computes the constant coefficient. Here the extra factor `T² - 1` clears every
matched pole. On a finite window of Laurent exponents the two resulting
Wick expansions agree, so the even coefficients of the original commutator
all equal its constant coefficient. Widening the mode cutoff permits any
integer shift. We use Khoruzhii's integer-valued doubled energies throughout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open LaurentPolynomial

/-- Multiplication by the Laurent binomial gives the difference of consecutive
coefficients of the same parity. -/
theorem coeff_T_two_sub_one_mul {R : Type*} [Ring R]
    (f : LaurentPolynomial R) (j : ℤ) :
    ((T 2 - 1) * f).coeff j = f.coeff (j - 2) - f.coeff j := by
  rw [sub_mul, one_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, T,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_add_eq_sub]

/-- If the Laurent binomial clears the coefficients in a symmetric window, all
even coefficients of the original polynomial in that window equal its constant term. -/
theorem even_coeff_eq_zero_coeff {R : Type*} [Ring R]
    (f : LaurentPolynomial R) (B : ℤ)
    (h : ∀ j : ℤ, |j| ≤ B → ((T 2 - 1) * f).coeff j = 0)
    (k : ℤ) (hk : |2 * k| ≤ B) :
    f.coeff (2 * k) = f.coeff 0 := by
  have step (j : ℤ) (hj : -B ≤ j ∧ j ≤ B) : f.coeff (j - 2) = f.coeff j := by
    exact sub_eq_zero.mp ((coeff_T_two_sub_one_mul f j).symm.trans (h j (abs_le.mpr hj)))
  rw [abs_le] at hk
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [← step _ hk]
    have he : 2 * ((n : ℤ) + 1) - 2 = 2 * (n : ℤ) := by omega
    rw [he]
    exact ih (by omega)
  | pred n ih =>
    have hs := step (2 * -(n : ℤ)) (by omega)
    have he : 2 * (-(n : ℤ) - 1) = 2 * -(n : ℤ) - 2 := by omega
    rw [he, hs]
    exact ih (by omega)

end Crossing

set_option autoImplicit false

open scoped BigOperators
namespace Crossing

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
variable (R : Type*) [CommRing R]

private theorem coeff_mul_shift (p : LaurentPolynomial R) (k : ℤ) :
    (p * LaurentPolynomial.T (-k)).coeff 0 = p.coeff k := by
  change (p * AddMonoidAlgebra.single (-k) (1 : R)).coeff 0 = p.coeff k
  simp only [AddMonoidAlgebra.coeff_mul_single_apply, neg_neg, zero_add, mul_one]

private theorem coeff_weighted_scalar (c : R) (s p v : LaurentPolynomial R) (k : ℤ) :
    (s * (LaurentPolynomial.C c * p) * v).coeff k = c * (s * p * v).coeff k := by
  have he : s * (LaurentPolynomial.C c * p) * v = LaurentPolynomial.C c * (s * p * v) := by ring
  rw [he, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply]
  simp

private theorem shifted_replacements (L e K W w d : ℕ) (k : ℤ) (P : List (ℕ × ℕ))
    (hpole : poleSum P ≤ d) (hdegree : 2 * d + 2 = W + w)
    (hleft : pairedLeftWeight P ≤ w) (hright : pairedRightWeight P ≤ W)
    (hw : w ≤ W) (hcut : e + K + W ≤ 2 * L) (hk : -(K : ℤ) ≤ k ∧ k ≤ K)
    (v : LaurentPolynomial R)
    (hu : UpperBound R v ((e : ℤ) - (w - pairedLeftWeight P : ℕ)))
    (hl : LowerBound R v (-(e : ℤ) - (w - pairedLeftWeight P : ℕ))) :
    ((((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
        (P.map fun p => forwardTail R 0 L p.1 p.2).prod * v).coeff k =
      (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ (d - poleSum P) *
        (P.map (pairConstant R)).prod * v).coeff k) ∧
    ((((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
        (P.map fun p => reverseTail R 0 L p.1 p.2).prod * v).coeff k =
      (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ (d - poleSum P) *
        (P.map fun p => -pairConstant R p).prod * v).coeff k) := by
  have htu : UpperBound R (LaurentPolynomial.T (-k)) (-k) := by
    simpa using upperBound_monomial R 1 (-k) (-k) le_rfl
  have htl : LowerBound R (LaurentPolynomial.T (-k)) (-k) := by
    simpa using lowerBound_monomial R 1 (-k) (-k) le_rfl
  have hu' := upperBound_mono R (upperBound_mul R hu htu)
    (show (e : ℤ) - (w - pairedLeftWeight P : ℕ) + -k ≤
      (↑(e + K) : ℤ) - (w - pairedLeftWeight P : ℕ) by omega)
  have hl' := lowerBound_mono R (lowerBound_mul R hl htl)
    (show -(↑(e + K) : ℤ) - (w - pairedLeftWeight P : ℕ) ≤
      -(e : ℤ) - (w - pairedLeftWeight P : ℕ) + -k by omega)
  obtain ⟨hf, hr⟩ := cutoff_partial_replacements R L (e + K) W w d P hpole
    hdegree hleft hright hw hcut (v * LaurentPolynomial.T (-k)) hu' hl'
  rw [← mul_assoc _ v _, coeff_mul_shift, ← mul_assoc _ v _, coeff_mul_shift] at hf hr
  exact ⟨hf, hr⟩

private theorem forward_actualTerm_local (L K : ℕ) {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr)) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + K + sourceEnergy B + 2 ≤ 2 * L)
    (k : ℤ) (hk : -(K : ℤ) ≤ k ∧ k ≤ K) :
    (actualTerm R L (d + 1) t I J).coeff k = (commonTerm R L (d + 1) t I J).coeff k := by
  have hp : poleSum (orientedPairs t) ≤ d + 1 := by
    by_cases hempty : t.remaining = []
    · exact (forward_full_pole ht hempty d hdegree).le
    · exact Nat.le_succ_of_le (forward_partial_pole ht hempty d hdegree)
  have hleft := forward_left_conservation ht
  have hright := forward_right_conservation ht
  have hv := forward_partial_coefficient_bounds R L ht I J hIJ
  rw [actualTerm, forward_matching_coefficient R L ht, coeff_weighted_scalar,
    commonTerm, ite_eq_left hp, forward_common_coefficient R ht, coeff_weighted_scalar]
  exact congrArg (fun a : R => (t.sign : R) * a)
    (shifted_replacements R L (doubledEnergy I) K (sourceEnergy B + 2)
      (sourceEnergy A) (d + 1) k (orientedPairs t) hp (by omega) (by omega)
      (by omega) (by omega) (by omega) hk _ hv.1 hv.2).1

private theorem reverse_actualTerm_local (L K : ℕ) {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + K + sourceEnergy B + 2 ≤ 2 * L)
    (k : ℤ) (hk : -(K : ℤ) ≤ k ∧ k ≤ K) :
    (actualTerm R L (d + 1) t I J).coeff k = (commonTerm R L (d + 1) t I J).coeff k := by
  have hp : poleSum (orientedPairs t) ≤ d + 1 := by
    by_cases hempty : t.remaining = []
    · exact (reverse_full_pole ht hempty d hdegree).le
    · exact Nat.le_succ_of_le (reverse_partial_pole ht hempty d hdegree)
  have hleft := reverse_left_conservation ht
  have hright := reverse_right_conservation ht
  have hv := reverse_partial_coefficient_bounds R L ht I J hIJ
  rw [actualTerm, reverse_matching_coefficient R L ht, coeff_weighted_scalar,
    commonTerm, ite_eq_left hp, reverse_common_coefficient R ht, coeff_weighted_scalar]
  exact congrArg (fun a : R => (t.sign : R) * a)
    (shifted_replacements R L (doubledEnergy I) K (sourceEnergy B + 2)
      (sourceEnergy A) (d + 1) k (orientedPairs t) hp (by omega) (by omega)
      (by omega) (by omega) (by omega) hk _ hv.1 hv.2).2

/-- Extracting a Laurent coefficient commutes with the sum over Wick matchings. -/
private theorem wickCoeff_list_sum (P : List (LaurentPolynomial R)) (k : ℤ) :
    P.sum.coeff k = (P.map fun p => p.coeff k).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.sum_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ih, List.map_cons]

private theorem productPolynomial_coeff_of_terms (L d : ℕ) (A B : List SourceIndex)
    (I J : Finset ℕ) (k : ℤ)
    (h : ∀ t ∈ Matching.terms A B,
      (actualTerm R L d t I J).coeff k = (commonTerm R L d t I J).coeff k) :
    (productPolynomial R L d A B I J).coeff k =
      (((Matching.terms A B).map fun t => commonTerm R L d t I J).sum).coeff k := by
  rw [productPolynomial_eq_sum, wickCoeff_list_sum, wickCoeff_list_sum]
  simp only [List.map_map, Function.comp_def]
  exact congrArg List.sum (List.map_congr_left h)

/-- When the multiplier cancels every pole at a specified coefficient, the signed
commutator vanishes at that coefficient. The two products use opposite normal orders. -/
theorem weighted_matrix_locality_of_terms (L d : ℕ) (A B I J : Index L) (k : ℤ)
    (hforward : ∀ t ∈ Matching.terms (A.val.sort.map Sum.inl) (B.val.sort.map Sum.inr),
      (actualTerm R L d t I.val J.val).coeff k = (commonTerm R L d t I.val J.val).coeff k)
    (hreverse : ∀ t ∈ Matching.terms (B.val.sort.map Sum.inr) (A.val.sort.map Sum.inl),
      (actualTerm R L d t I.val J.val).coeff k = (commonTerm R L d t I.val J.val).coeff k) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
        (scaledMatrix R L A * constantMatrix R L B) I J).coeff k -
      ((-1 : ℤˣ) ^ (A.val.sort.length * B.val.sort.length)) •
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
          (constantMatrix R L B * scaledMatrix R L A) I J).coeff k = 0 := by
  let u : ℤˣ := (-1) ^ (A.val.sort.length * B.val.sort.length)
  have h : (productPolynomial R L d (A.val.sort.map Sum.inl) (B.val.sort.map Sum.inr)
      I.val J.val).coeff k = u • (productPolynomial R L d (B.val.sort.map Sum.inr)
      (A.val.sort.map Sum.inl) I.val J.val).coeff k := by
    rw [productPolynomial_coeff_of_terms R _ _ _ _ _ _ _ hforward,
      productPolynomial_coeff_of_terms R _ _ _ _ _ _ _ hreverse]
    simpa only [u, Units.smul_def, AddMonoidAlgebra.coeff_smul_apply] using
      congrArg (fun p : LaurentPolynomial R => p.coeff k)
        (common_sum_exchange R L d A.val.sort B.val.sort I.val J.val)
  rw [forward_productPolynomial_matrix, reverse_productPolynomial_matrix] at h
  have hC : (dualSign J.val : LaurentPolynomial R) = LaurentPolynomial.C (dualSign J.val : R) :=
    by simp
  rw [hC] at h
  simp only [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
    neg_zero, zero_add] at h
  let e : R := (dualSign J.val : R)
  have hs : e * e = 1 := by
    simpa only [e, Int.cast_mul, Int.cast_one] using
      congrArg (fun z : ℤ => (z : R)) (dualSign_mul_self J.val)
  let a := ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
    (scaledMatrix R L A * constantMatrix R L B) I J).coeff k
  let b := ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
    (constantMatrix R L B * scaledMatrix R L A) I J).coeff k
  change e * a = u • (e * b) at h
  change a - u • b = 0
  apply sub_eq_zero.mpr
  calc
    a = e * (e * a) := by rw [← mul_assoc, hs, one_mul]
    _ = e * (u • (e * b)) := by rw [h]
    _ = u • b := by
      simp only [Units.smul_def, zsmul_eq_mul]
      calc
        _ = (u : ℤ) * ((e * e) * b) := by ring
        _ = _ := by rw [hs, one_mul]

/-- The residue of the two ordered fermion fields at every even Laurent exponent in
the cutoff window. Exponent `2 * j` corresponds to the bivariate coefficient with
paper shift `s = -j-1`. -/
theorem shifted_weighted_matrix_residue (L K : ℕ) (A B I J : Index L) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A.val.sort + sourceEnergy B.val.sort)
    (hw : sourceEnergy A.val.sort ≤ sourceEnergy B.val.sort)
    (hIJ : doubledEnergy I.val = doubledEnergy J.val)
    (hcut : doubledEnergy I.val + K + sourceEnergy B.val.sort + 2 ≤ 2 * L)
    (j : ℤ) (hj : |2 * j| ≤ K) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
        (scaledMatrix R L A * constantMatrix R L B) I J).coeff (2 * j) -
      ((-1 : ℤˣ) ^ (A.val.sort.length * B.val.sort.length)) •
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
          (constantMatrix R L B * scaledMatrix R L A) I J).coeff (2 * j) =
      (if I = J then (1 : R) else 0) * matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B := by
  let x := (scaledMatrix R L A * constantMatrix R L B) I J
  let y := (constantMatrix R L B * scaledMatrix R L A) I J
  let u : ℤˣ := (-1 : ℤˣ) ^ (A.val.sort.length * B.val.sort.length)
  let t := LaurentPolynomial.T (R := R) 2 - 1
  let f (a : ℕ) := t ^ a * x - LaurentPolynomial.C ((u : ℤ) : R) * (t ^ a * y)
  have hcoeff (a : ℕ) (k : ℤ) :
      (f a).coeff k = (t ^ a * x).coeff k - u • (t ^ a * y).coeff k := by
    simp only [f, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, ← LaurentPolynomial.single_eq_C,
      AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add, Units.smul_def, zsmul_eq_mul]
  have hmul : t * f d = f (d + 1) := by
    dsimp only [f]
    rw [pow_succ]
    ring
  have hlocal (k : ℤ) (hk : |k| ≤ K) : (t * f d).coeff k = 0 := by
    rw [hmul, hcoeff]
    apply weighted_matrix_locality_of_terms R L (d + 1) A B I J k
    · intro m hm
      exact forward_actualTerm_local R L K hm d hdegree hw I.val J.val hIJ hcut k (abs_le.mp hk)
    · intro m hm
      exact reverse_actualTerm_local R L K hm d hdegree hw I.val J.val hIJ hcut k (abs_le.mp hk)
  have he := VPVNP.Crossing.even_coeff_eq_zero_coeff (f d) (K : ℤ) hlocal j hj
  rw [hcoeff, hcoeff] at he
  exact he.trans (weighted_matrix_residue R L A B I J d hdegree hw hIJ (by omega))

end Crossing

open Lemmata.FockCircuits
open Lemmata.FockCircuits.FiniteIdentity
namespace Crossing

private def mapTerm {α β : Type*} (f : α → β) (t : Matching.Term α) : Matching.Term β :=
  ⟨t.sign, t.pairs.map (Prod.map f f), t.remaining.map f⟩

private lemma map_terms {α β : Type*} (f : α → β) (A B : List α) :
    (Matching.terms A B).map (mapTerm f) = Matching.terms (A.map f) (B.map f) := by
  induction A generalizing B with
  | nil => simp [Matching.terms, mapTerm]
  | cons a A ih =>
    simp only [List.map_cons, Matching.terms, List.map_append, List.map_map,
      List.map_flatten, List.map_ofFn]
    congr 1
    · rw [← ih]
      simp only [List.map_map]
      rfl
    · apply congrArg List.flatten
      rw [List.ofFn_congr (List.length_map (f := f) (as := B)).symm]
      apply congrArg List.ofFn
      funext j
      simp only [Function.comp_def, Fin.val_cast, List.map_map, List.eraseIdx_map,
        ← ih, Fin.getElem_fin, List.getElem_map, List.length_map]
      rfl

private theorem reverseFullSum_eq_swapped (R : Type*) [CommRing R] (A B : List ℕ) :
    reverseFullSum R A B =
      fullMatchingSum R
        (Matching.crossGamma R fun m n => (Fock.contractionCoefficient m n : R))
        (Matching.terms (B.map Sum.inl) (A.map Sum.inr)) := by
  let flip : SourceIndex → SourceIndex := Sum.elim Sum.inr Sum.inl
  have h := map_terms flip (B.map Sum.inr) (A.map Sum.inl)
  have hB : (B.map Sum.inr).map flip = B.map Sum.inl := by simp [flip, List.map_map]
  have hA : (A.map Sum.inl).map flip = A.map Sum.inr := by simp [flip, List.map_map]
  rw [hB, hA] at h
  rw [reverseFullSum, ← h, fullMatchingSum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_def, mapTerm, List.map_eq_nil_iff]
  split_ifs
  · unfold Matching.coefficient
    congr 1
    unfold orientedPairs
    simp only [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    obtain ⟨hl, hr⟩ := Matching.pair_mem_sources ht hp
    obtain ⟨n, _, hn⟩ := List.mem_map.mp hl
    obtain ⟨m, _, hm⟩ := List.mem_map.mp hr
    have he : p = (Sum.inr n, Sum.inl m) := Prod.ext hn.symm hm.symm
    rw [he]
    rfl
  · rfl

/-- Transposing the two operator-source labels gives the sign from reflecting
the variable difference and exchanging the two fermionic blocks. -/
theorem matrix_vacuum_exchange (R : Type*) [CommRing R] (L : ℕ) (A B : Index L) (d : ℕ)
    (hd : 2 * d + 2 = sourceEnergy A.val.sort + sourceEnergy B.val.sort) :
    matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B =
      ((-1 : ℤˣ) ^ (A.val.sort.length * B.val.sort.length)) •
        ((-1 : R) ^ (d + 1) * matrix R L (Pi.single B 1) ⟨∅, by simp⟩ A) := by
  rw [matrix_single_vacuum_eq_fullMatchingSum, matrix_single_vacuum_eq_fullMatchingSum,
    fullMatchingSum_exchange R _ _ d hd, reverse_fullMatchingSum R _ _ d hd,
    reverseFullSum_eq_swapped]

end Crossing

namespace Crossing

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

section
open LaurentPolynomial

/-- Inverting the Laurent variable reflects the pole-clearing multiplier. -/
private theorem invert_multiplier (d : ℕ) :
    invert ((T (R := R) 2 - 1) ^ d) = (-1) ^ d * T (-(2 * (d : ℤ))) * (T 2 - 1) ^ d := by
  have ht : T (R := R) (-2) * T 2 = 1 := by rw [← T_add]; norm_num
  have h : T (R := R) (-2) - 1 = -1 * T (-2) * (T 2 - 1) := by
    rw [neg_one_mul, neg_mul, mul_sub, mul_one, ht]
    ring
  simp only [map_pow, map_sub, invert_T, map_one]
  rw [h, mul_pow, mul_pow, T_pow]
  congr 2
  ring_nf

private theorem shift_coeff (f : LaurentPolynomial R) (n j : ℤ) :
    (T n * f).coeff j = f.coeff (j - n) := by
  rw [T, AddMonoidAlgebra.coeff_single_mul_apply]
  simp [sub_eq_add_neg, add_comm]

/-- For equal external energy, the Laurent powers of the two fields in a matrix-product
entry add to minus the sum of the two source energies. Swapping the source whose Laurent
variable is recorded reflects the index about `-1`. -/
private theorem reflected_term (w W x y : ℤ) (d : ℕ) (s : ℤ) (v : R)
    (hd : 2 * (d : ℤ) + 2 = w + W) (hxy : x + y = -(w + W)) :
    ((T (R := R) 2 - 1) ^ d * (C v * T x)).coeff (2*s) =
      (-1) ^ d * ((T (R := R) 2 - 1) ^ d * (C v * T y)).coeff (-2*s-2) := by
  have h := invert_multiplier (R := R) d
  have ht : T (R := R) (-(2*(d:ℤ))) * T (-y) = T 2 * T x := by
    rw [← T_add, ← T_add]
    congr 1
    omega
  have he : invert ((T (R := R) 2 - 1) ^ d * (C v * T y)) =
      C ((-1 : R) ^ d) * (T 2 * ((T 2 - 1) ^ d * (C v * T x))) := by
    simp only [map_mul, h, invert_C, invert_T]
    rw [map_pow, map_neg, map_one]
    calc
      _ = (-1) ^ d * ((T (R := R) 2 - 1) ^ d * C v) *
          (T (-(2*(d:ℤ))) * T (-y)) := by ring
      _ = _ := by rw [ht]; ring
  have hec := congrArg (fun f : LaurentPolynomial R => f.coeff (2*s+2)) he
  simp only [invert_apply, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
    neg_zero, zero_add, shift_coeff] at hec
  rw [show -(2 * s + 2) = -2*s - 2 by ring, add_sub_cancel_right] at hec
  simp only [LaurentPolynomial.single_eq_C] at hec
  have hs : (-1 : R) ^ d * (-1) ^ d = 1 := by rw [← mul_pow]; simp
  rw [hec, ← mul_assoc ((-1 : R) ^ d), hs, one_mul]


end
private theorem reflect_mode_mul_constant (c c' : R) (e : ℤ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T (R := R) e) * LaurentPolynomial.C c' =
      LaurentPolynomial.C (c*c') * LaurentPolynomial.T e := by
  rw [map_mul]
  ring

private theorem reflect_constant_mul_mode (c c' : R) (e : ℤ) :
    LaurentPolynomial.C c * (LaurentPolynomial.C c' * LaurentPolynomial.T (R := R) e) =
      LaurentPolynomial.C (c*c') * LaurentPolynomial.T e := by
  rw [map_mul, mul_assoc]



/-- Switching the field that carries the Laurent variable reflects the selected
coefficient and interchanges the two ordered products. -/
private theorem forward_matrix_reflect (L d : ℕ) (A B I J : Index L) (j : ℤ)
    (hd : 2 * d + 2 = doubledEnergy A.val + doubledEnergy B.val)
    (hIJ : doubledEnergy I.val = doubledEnergy J.val) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (scaledMatrix R L A * constantMatrix R L B) I J).coeff (2 * j) =
      (-1) ^ d * ((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (constantMatrix R L A * scaledMatrix R L B) I J).coeff (-2 * j - 2) := by
  classical
  simp only [Matrix.mul_apply, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    scaledMatrix_eq_monomial, constantMatrix, reflect_mode_mul_constant, reflect_constant_mul_mode]
  apply Finset.sum_congr rfl
  intro K _
  exact reflected_term R (doubledEnergy A.val) (doubledEnergy B.val) _ _ d j _ (by omega) (by omega)

private theorem reverse_matrix_reflect (L d : ℕ) (A B I J : Index L) (j : ℤ)
    (hd : 2 * d + 2 = doubledEnergy A.val + doubledEnergy B.val)
    (hIJ : doubledEnergy I.val = doubledEnergy J.val) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (constantMatrix R L B * scaledMatrix R L A) I J).coeff (2 * j) =
      (-1) ^ d * ((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (scaledMatrix R L B * constantMatrix R L A) I J).coeff (-2 * j - 2) := by
  classical
  simp only [Matrix.mul_apply, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    scaledMatrix_eq_monomial, constantMatrix, reflect_mode_mul_constant, reflect_constant_mul_mode]
  apply Finset.sum_congr rfl
  intro K _
  exact reflected_term R (doubledEnergy A.val) (doubledEnergy B.val) _ _ d j _ (by omega) (by omega)

/-- The Laurent coefficient of the signed commutator at `2j` in orientation `(A,B)`
is the coefficient at `2(-j - 1)` in the opposite orientation, up to the explicit sign. -/
theorem commutator_reflect (L d : ℕ) (A B I J : Index L) (j : ℤ)
    (hd : 2 * d + 2 = sourceEnergy A.val.sort + sourceEnergy B.val.sort)
    (hIJ : doubledEnergy I.val = doubledEnergy J.val) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (scaledMatrix R L A * constantMatrix R L B) I J).coeff (2 * j) -
      ((-1 : ℤˣ) ^ (A.val.sort.length * B.val.sort.length)) •
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (constantMatrix R L B * scaledMatrix R L A) I J).coeff (2 * j) =
      -(((-1 : ℤˣ) ^ (A.val.sort.length * B.val.sort.length)) • ((-1 : R) ^ d)) *
      (((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (scaledMatrix R L B * constantMatrix R L A) I J).coeff (2 * (-j - 1)) -
        ((-1 : ℤˣ) ^ (B.val.sort.length * A.val.sort.length)) •
          ((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (constantMatrix R L A * scaledMatrix R L B) I J).coeff (2 * (-j - 1))) := by
  rw [sourceEnergy_sort, sourceEnergy_sort] at hd
  rw [forward_matrix_reflect R L d A B I J j hd hIJ, reverse_matrix_reflect R L d A B I J j hd hIJ,
    show 2 * (-j - 1) = -2 * j - 2 by ring, Nat.mul_comm (B.val.sort (· ≤ ·)).length (A.val.sort (· ≤ ·)).length]
  simp only [Units.smul_def, zsmul_eq_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  generalize ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
    (scaledMatrix R L B * constantMatrix R L A) I J).coeff (-2 * j - 2) = a
  generalize ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
    (constantMatrix R L A * scaledMatrix R L B) I J).coeff (-2 * j - 2) = b
  generalize (A.val.sort (· ≤ ·)).length * (B.val.sort (· ≤ ·)).length = n
  have hs : (-1 : R)^n * (-1)^n = 1 := by rw [← mul_pow]; simp
  linear_combination (-1 : R) ^ d * b * (Eq.symm hs)


/-- The shifted coefficient identity in both orientations of the input blocks. A single
cutoff suffices for exponent `2 * j` and its reflected exponent `2 * (-j - 1)`. -/
theorem shifted_weighted_matrix_residue_all (L K : ℕ) (A B I J : Index L) (d : ℕ)
    (hd : 2 * d + 2 = sourceEnergy A.val.sort + sourceEnergy B.val.sort)
    (hIJ : doubledEnergy I.val = doubledEnergy J.val)
    (hcut : doubledEnergy I.val + K + max (sourceEnergy A.val.sort) (sourceEnergy B.val.sort) + 4 ≤ 2 * L)
    (j : ℤ) (hj : |2 * j| ≤ K) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (scaledMatrix R L A * constantMatrix R L B) I J).coeff (2 * j) -
      ((-1 : ℤˣ) ^ (A.val.sort.length * B.val.sort.length)) •
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d * (constantMatrix R L B * scaledMatrix R L A) I J).coeff (2 * j) =
      (if I = J then (1 : R) else 0) * matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B := by
  by_cases h : sourceEnergy A.val.sort ≤ sourceEnergy B.val.sort
  · exact shifted_weighted_matrix_residue R L K A B I J d hd h hIJ (by omega) j hj
  rw [commutator_reflect R L d A B I J j hd hIJ]
  have hba : 2 * d + 2 = sourceEnergy B.val.sort + sourceEnergy A.val.sort := by omega
  have hj' : |2 * (-j - 1)| ≤ (K+2 : ℕ) := by
    have := abs_le.mp hj
    exact abs_le.mpr (by omega)
  rw [shifted_weighted_matrix_residue R L (K + 2) B A I J d hba (by omega) hIJ (by omega) (-j - 1) hj',
    VPVNP.Crossing.matrix_vacuum_exchange R L A B d hd]
  simp only [Units.smul_def, zsmul_eq_mul, pow_succ (-1 : R) d]
  ring

end Crossing

end VPVNP
end Computability
end OAI
