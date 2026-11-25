import OAI.Computability.NearSquareRoot.InterchangeLabels
import OAI.Computability.NearSquareRoot.InterchangeOuter
import OAI.Computability.NearSquareRoot.InterchangeOuterSize

/-! # Rank saving for the two-level interchange label matrix -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

theorem card_word (p q : ℕ) : Fintype.card (Word p q) = q ^ (2*p-1) := by
  simp [Word]

theorem card_label (p q : ℕ) :
    Fintype.card (Label p q) = (q ^ (2*p-1)) ^ (2*p-1) := by
  simp [Label, Word]

theorem hammingLabelMatrix_eq_outer (p q : ℕ) [Fact p.Prime] :
    hammingLabelMatrix p q =
      outerLabelMatrix (innerLeft p q * innerRight p q) (2*p-1) (p-1) := by
  rw [← innerMatrix_factor]
  ext v w
  rw [hammingLabelMatrix_apply, cast_hammingDist]
  rfl

/-- The relative rank is at most a constant depending only on the characteristic
times `q^(-p²)`, for every positive alphabet size, including small alphabets. -/
theorem hammingLabelMatrix_rank_saving (p q : ℕ) [Fact p.Prime] (hq : 0 < q) :
    (hammingLabelMatrix p q).rank * q ^ (p^2) ≤
      (1 + (2*p-1)^(p-1))^(p^2) * Fintype.card (Label p q) := by
  let h := 2*p-1
  let t := p-1
  let c := 1 + h^t
  have hp := (Fact.out : p.Prime).two_le
  change _ ≤ c^(p^2) * _
  by_cases hlarge : c ≤ q
  · have hdim : Fintype.card (InnerFeature p q) ≤ Fintype.card (Word p q) := by
      rw [card_word, card_innerFeature, ← mul_pow]
      exact innerLabelFeatureCount_le_wordCount (by omega) hlarge
    have hr := outerLabelMatrix_rank_le (innerLeft p q) (innerRight p q)
      (h := h) (t := t) (by dsimp [h,t]; omega) hdim
    rw [← hammingLabelMatrix_eq_outer, card_innerFeature, ← mul_pow, card_word] at hr
    have he : 1 + (h-t) ≤ p^2 := by
      have hdiff : h-t = p := by dsimp [h,t]; omega
      rw [hdiff]
      nlinarith [show 0 ≤ (p-2) from Nat.zero_le _]
    calc
      _ ≤ (c * ((1 + (h*q)^t)^(h-t) * (q^h)^t)) * q^(p^2) :=
        Nat.mul_le_mul_right _ hr
      _ ≤ c^(1+(h-t)) * (q^h)^h := by
        rw [← mul_assoc c]
        exact outerLabelRankSavings (by omega : 0 < p) hq
      _ ≤ _ := by
        rw [card_label]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by dsimp [c]; omega) he)
  · calc
      _ ≤ Fintype.card (Label p q) * q^(p^2) :=
        Nat.mul_le_mul_right _ (Matrix.rank_le_card_width _)
      _ ≤ Fintype.card (Label p q) * c^(p^2) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := Nat.mul_comm ..

/-- For the specific dyadic choice of `q` in the interchange algorithm the
number of basis transfers, multiplied by the number of queries, is linear
in the total number of labels. -/
theorem batch_rank_cost (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) :
    let q := 2 ^ labelRadixExponent m (p^2)
    m * (hammingLabelMatrix p q).rank ≤
      (1 + (2*p-1)^(p-1))^(p^2) * Fintype.card (Label p q) := by
  let q := 2 ^ labelRadixExponent m (p^2)
  have hp := (Fact.out : p.Prime).pos
  have hmq : m ≤ q^(p^2) := (labelRadixExponent_spec hm (by positivity : 0 < p^2)).1
  calc
    m * (hammingLabelMatrix p q).rank ≤ q^(p^2) * (hammingLabelMatrix p q).rank :=
      Nat.mul_le_mul_right _ hmq
    _ = _ := Nat.mul_comm ..
    _ ≤ _ := hammingLabelMatrix_rank_saving p q (by dsimp [q]; positivity)

end Interchange

end NearSquareRoot
end Computability
end OAI
