import Mathlib.FieldTheory.Finite.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The inner low-rank Hamming matrix for address interchange

On words of length `2 * p - 1`, a Hamming distance divisible by the prime `p`
is either zero or `p`. Expanding the finite-field indicator gives a factorization
through one constant feature and tuples of `p - 1` positions and their letters.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

abbrev Word (p q : ℕ) := Fin (2 * p - 1) → Fin q

/-- The indicator for equality or distance `p` between two inner labels. -/
def innerMatrix (p q : ℕ) : Matrix (Word p q) (Word p q) (ZMod p) :=
  fun x y => if x = y ∨ hammingDist x y = p then 1 else 0

/-- The field polynomial detecting distance zero and distance `p`. -/
theorem equalOrFar_polynomial {α : Type*} [DecidableEq α] (p : ℕ) [Fact p.Prime]
    (x y : Fin (2 * p - 1) → α) :
    (if x = y ∨ hammingDist x y = p then 1 else 0 : ZMod p) =
      1 - (hammingDist x y : ZMod p) ^ (p - 1) := by
  have hlt : hammingDist x y < 2 * p := by
    have hp := (Fact.out : p.Prime).pos
    have := hammingDist_le_card_fintype (x := x) (y := y)
    simpa using this.trans_lt (by simpa using (show 2 * p - 1 < 2 * p by omega))
  have hd : p ∣ hammingDist x y ↔ x = y ∨ hammingDist x y = p := by
    constructor
    · rintro ⟨k, hk⟩
      rcases k with _ | _ | k
      · left
        exact hammingDist_eq_zero.mp (by simpa using hk)
      · right
        simpa using hk
      · have hk' : 2 * p ≤ hammingDist x y := by
          rw [hk, Nat.mul_comm 2 p]
          exact Nat.mul_le_mul_left p (by omega)
        omega
    · rintro (rfl | h)
      · simp
      · simp [h]
  rw [ZMod.pow_card_sub_one]
  by_cases h : x = y ∨ hammingDist x y = p
  · have hz := (CharP.cast_eq_zero_iff (ZMod p) p _).mpr (hd.mpr h)
    simp [h, hz]
  · have hz : (hammingDist x y : ZMod p) ≠ 0 :=
      fun hc => h (hd.mp ((CharP.cast_eq_zero_iff (ZMod p) p _).mp hc))
    simp [h, hz]

theorem innerMatrix_apply (p q : ℕ) [Fact p.Prime] (x y : Word p q) :
    innerMatrix p q x y = 1 - (hammingDist x y : ZMod p) ^ (p - 1) :=
  equalOrFar_polynomial p x y

abbrev Positions (p : ℕ) := Fin (p - 1) → Fin (2 * p - 1)
abbrev Letters (p q : ℕ) := Fin (p - 1) → Fin q

/-- An ordered monomial together with the values of the row word at its positions. -/
abbrev InnerFeature (p q : ℕ) := Unit ⊕ (Positions p × Letters p q)

def innerLeft (p q : ℕ) : Matrix (Word p q) (InnerFeature p q) (ZMod p)
  | _, .inl _ => 1
  | x, .inr (positions, letters) => if letters = x ∘ positions then 1 else 0

def innerRight (p q : ℕ) : Matrix (InnerFeature p q) (Word p q) (ZMod p)
  | .inl _, _ => 1
  | .inr (positions, letters), y =>
    -(∏ i, if letters i ≠ y (positions i) then 1 else 0)

theorem cast_hammingDist {ι α : Type*} [Fintype ι] [DecidableEq α] (p : ℕ)
    (x y : ι → α) :
    (hammingDist x y : ZMod p) = ∑ i, if x i ≠ y i then 1 else 0 := by
  simp only [hammingDist, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]

/-- Explicit factorization of the equal-or-far matrix over the data field. -/
theorem innerMatrix_factor (p q : ℕ) [Fact p.Prime] :
    innerMatrix p q = innerLeft p q * innerRight p q := by
  ext x y
  rw [innerMatrix_apply, cast_hammingDist, Fintype.sum_pow, Matrix.mul_apply,
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [innerLeft, innerRight, ite_mul, Function.comp_def, sub_eq_add_neg]

theorem card_innerFeature (p q : ℕ) :
    Fintype.card (InnerFeature p q) = 1 + (2 * p - 1) ^ (p - 1) * q ^ (p - 1) := by
  simp [InnerFeature, Positions, Letters]

theorem innerMatrix_rank_le (p q : ℕ) [Fact p.Prime] :
    (innerMatrix p q).rank ≤ 1 + (2 * p - 1) ^ (p - 1) * q ^ (p - 1) := by
  rw [innerMatrix_factor, ← card_innerFeature]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- An outer label consists of a word of inner labels. -/
abbrev Label (p q : ℕ) := Fin (2 * p - 1) → Word p q

/-- Each off-diagonal pair differs in exactly `p` outer positions. In each
differing position the inner words have Hamming distance exactly `p`. -/
def hammingLabelMatrix (p q : ℕ) : Matrix (Label p q) (Label p q) (ZMod p) :=
  fun v w => if v = w ∨
    (hammingDist v w = p ∧ ∀ i, v i ≠ w i → hammingDist (v i) (w i) = p) then 1 else 0

/-- Entrywise polynomial used for the two-level factorization. -/
theorem hammingLabelMatrix_apply (p q : ℕ) [Fact p.Prime] (v w : Label p q) :
    hammingLabelMatrix p q v w =
      (1 - (hammingDist v w : ZMod p) ^ (p - 1)) * ∏ i, innerMatrix p q (v i) (w i) := by
  classical
  rw [← equalOrFar_polynomial p v w]
  by_cases h : ∀ i, v i = w i ∨ hammingDist (v i) (w i) = p
  · have h' : ∀ i, v i ≠ w i → hammingDist (v i) (w i) = p :=
      fun i hi => (h i).resolve_left hi
    unfold hammingLabelMatrix
    rw [if_congr (or_congr_right (and_iff_left h')) rfl rfl]
    simp [innerMatrix, h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hvw : v ≠ w := fun heq => hi (.inl (congrFun heq i))
    have h' : ¬ (∀ i, v i ≠ w i → hammingDist (v i) (w i) = p) :=
      fun heq => hi (.inr (heq i (fun hEq => hi (.inl hEq))))
    have hz : ∏ j, innerMatrix p q (v j) (w j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [innerMatrix, hi])
    simp [hammingLabelMatrix, hvw, h', hz]

end Interchange

end NearSquareRoot
end Computability
end OAI
