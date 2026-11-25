import Mathlib.Algebra.Polynomial.Taylor
import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetQuadratic

/-! # Coefficient recursion for denominator-free Taylor shifts

Write a polynomial of length `2n` as a low half plus a high half times `X^n`.
After translating the variable, the multiplier is `(X + C a)^n`, whose product
with the shifted high half is one ordinary open convolution over the base ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped Classical

variable {R : Type*} [CommRing R]

/-- A coefficient vector in ascending order of powers. -/
noncomputable def vectorPolynomial {n : ℕ} (x : Fin n → R) : R[X] :=
  ∑ i : Fin n, monomial i.val (x i)

/-- The coefficient of degree `k` after substituting `X + a` for `X`. -/
noncomputable def shiftedCoefficient (a : R) {n : ℕ} (x : Fin n → R) (k : ℕ) : R :=
  ((vectorPolynomial x).comp (X + C a)).coeff k

/-- Extend a finite vector by zeros to a new range of indices. -/
def taylorPad {S : Type*} [Zero S] {n m : ℕ} (x : Fin n → S) (j : Fin m) : S :=
  if h : j.val < n then x ⟨j.val, h⟩ else 0

theorem vectorPolynomial_eq_ofFn {n : ℕ} (x : Fin n → R) : vectorPolynomial x = ofFn n x :=
  (ofFn_eq_sum_monomial x).symm

theorem vectorPolynomial_pad {n m : ℕ} (hnm : n ≤ m) (x : Fin n → R) :
    vectorPolynomial (taylorPad (m := m) x) = vectorPolynomial x := by
  simp only [vectorPolynomial_eq_ofFn]
  ext k
  by_cases hk : k < n
  · rw [ofFn_coeff_eq_val_of_lt _ (hk.trans_le hnm), ofFn_coeff_eq_val_of_lt _ hk,
      taylorPad, dite_eq_left hk]
  · rw [ofFn_coeff_eq_zero_of_ge x (Nat.le_of_not_gt hk)]
    by_cases hkm : k < m
    · rw [ofFn_coeff_eq_val_of_lt _ hkm, taylorPad, dite_eq_right hk]
    · exact ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hkm)

theorem shiftedCoefficient_pad (a : R) {n m : ℕ} (hnm : n ≤ m) (x : Fin n → R) (k : ℕ) :
    shiftedCoefficient a (taylorPad (m := m) x) k = shiftedCoefficient a x k := by
  simp only [shiftedCoefficient, vectorPolynomial_pad hnm]

theorem shiftedCoefficient_one (a : R) (x : Fin 1 → R) (k : Fin 1) :
    shiftedCoefficient a x k.val = x k := by
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  simp [shiftedCoefficient, vectorPolynomial]

/-- Translating the variable preserves the degree bound, including the empty vector. -/
theorem shiftedCoefficient_eq_zero_of_ge (a : R) {n : ℕ} (x : Fin n → R) {k : ℕ}
    (hk : n ≤ k) : shiftedCoefficient a x k = 0 := by
  change (taylor a (vectorPolynomial x)).coeff k = 0
  apply coeff_eq_zero_of_degree_lt
  rw [degree_taylor, vectorPolynomial_eq_ofFn]
  exact (ofFn_degree_lt x).trans_le (by exact_mod_cast hk)

theorem vectorPolynomial_split {n : ℕ} (x : Fin (n+n) → R) :
    vectorPolynomial x = vectorPolynomial (fun j => x (Fin.castAdd n j)) +
      vectorPolynomial (fun j => x (Fin.natAdd n j)) * X ^ n := by
  unfold vectorPolynomial
  rw [Fin.sum_univ_add, Finset.sum_mul]
  simp only [Fin.val_castAdd, Fin.val_natAdd, monomial_mul_X_pow, Nat.add_comm n]

private theorem pad_shiftedCoefficient (a : R) {n m : ℕ} (x : Fin n → R) (k : Fin m) :
    taylorPad (fun i : Fin n => shiftedCoefficient a x i.val) k = shiftedCoefficient a x k.val := by
  unfold taylorPad
  split
  · rfl
  · exact (shiftedCoefficient_eq_zero_of_ge a x (by omega)).symm

private theorem ofFn_taylorPad (a : R) {n : ℕ} (x : Fin n → R) :
    ofFn (n+1) (taylorPad (fun i : Fin n => shiftedCoefficient a x i.val)) =
      (vectorPolynomial x).comp (X + C a) := by
  ext k
  by_cases hk : k < n+1
  · rw [ofFn_coeff_eq_val_of_lt _ hk, pad_shiftedCoefficient]
    rfl
  · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]
    exact (shiftedCoefficient_eq_zero_of_ge a x (by omega)).symm

private theorem ofFn_taylorPower (a : R) (n : ℕ) :
    ofFn (n+1) (fun i => ((X + C a)^n).coeff i.val) = (X + C a)^n := by
  apply ofFn_comp_toFn_eq_id_of_natDegree_lt
  nontriviality R
  simp

/-- Splitting a length-`2n` Taylor shift into two length-`n` shifts and
one open convolution by a fixed vector. -/
theorem shiftedCoefficient_split (a : R) {n : ℕ} (x : Fin (n+n) → R) (k : Fin (n+n)) :
    shiftedCoefficient a x k.val =
      taylorPad (fun i : Fin n => shiftedCoefficient a (fun j => x (Fin.castAdd n j)) i.val) k +
      openConv R (n+1)
        (taylorPad (fun i : Fin n => shiftedCoefficient a (fun j => x (Fin.natAdd n j)) i.val))
        (fun i => ((X + C a)^n).coeff i.val) ⟨k.val, by omega⟩ := by
  rw [← ofFn_mul_coeff_openConv, ofFn_taylorPad, ofFn_taylorPower, pad_shiftedCoefficient]
  simp only [shiftedCoefficient, vectorPolynomial_split x, add_comp, mul_X_pow_comp, coeff_add]

end FiniteFourier
end LinearAlgebra
end OAI
