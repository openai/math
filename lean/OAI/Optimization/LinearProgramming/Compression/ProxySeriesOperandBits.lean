import OAI.Optimization.LinearProgramming.Compression.ProxySeriesCost
import OAI.Optimization.LinearProgramming.Compression.ProxyRegisterBits
import OAI.Optimization.LinearProgramming.Compression.RationalMinorSize

/-! Encoding lengths of the exact rational operands of each odd-series round. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open OAI.Optimization.LinearProgramming.PrimalDual (ratBits_mul_le ratBits_sub_le ratBits_inv_le ratBits_neg)

theorem ratBits_div_le (a b : ℚ) :
    ratBits (a / b) ≤ 3 + 2 * ratBits a + 4 * ratBits b := by
  rw [div_eq_mul_inv]
  have hm := ratBits_mul_le a b⁻¹
  have hi := ratBits_inv_le b
  omega

private theorem ratBits_pow_le (q : ℚ) (B n : ℕ) (hq : ratBits q ≤ B) :
    ratBits (q ^ n) ≤ 3 + 2 * (B*n) := by
  unfold ratBits at hq ⊢
  simp only [Rat.num_pow, Rat.den_pow, Int.natAbs_pow]
  have hmax (j : ℕ) (hj : j.log2 < B) : j ^ n ≤ 2 ^ (B*n) := by
    have h : j ≤ 2 ^ B :=
      Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    rw [pow_mul]
    exact Nat.pow_le_pow_left h _
  have hn := log2_le_of_le_two_pow (hmax q.num.natAbs (by omega))
  have hd := log2_le_of_le_two_pow (hmax q.den (by omega))
  omega

/-- A quadratic polynomial in the rational input size and in the number
of terms bounds each operand and result at a completed series round. -/
def seriesRegisterBase (B M : ℕ) : ℕ :=
  let W := 20*(B+5)
  let P := 3 + 2*(W*(2*M+2))
  let S := 3 + 2*(2*M*(2*M+W+1)+2*M+1)
  20*(B+W+P+S+2*M+10)

/-- Each class of rational that the recurrence writes before the final division. -/
structure SeriesOperands (z : ℚ) (M H : ℕ) : Prop where
  input : ratBits z ≤ H
  minusOne : ratBits (z-1) ≤ H
  plusOne : ratBits (z+1) ≤ H
  argument : ratBits ((z-1)/(z+1)) ≤ H
  power : ∀ j ≤ 2*M+2, ratBits (((z-1)/(z+1)) ^ j) ≤ H
  oddDenominator : ∀ j ≤ 2*M+2, ratBits (j : ℚ) ≤ H
  term : ∀ j ≤ 2*M+2, ratBits (((z-1)/(z+1)) ^ j / (j:ℚ)) ≤ H
  sum : ∀ i ≤ M, ratBits (oddPartial ((z-1)/(z+1)) i) ≤ H
  result : ∀ i ≤ M, ratBits (logTruncation z i) ≤ H

theorem logSeriesOperand_bits {z : ℚ} (hz : 1 ≤ z) {B : ℕ} (hB : ratBits z ≤ B) (M : ℕ) :
    SeriesOperands z M (seriesRegisterBase B M) := by
  let w := (z-1)/(z+1)
  let W := 20*(B+5)
  let P := 3 + 2*(W*(2*M+2))
  let S := 3 + 2*(2*M*(2*M+W+1)+2*M+1)
  let H := 20*(B+W+P+S+2*M+10)
  change SeriesOperands z M H
  have h1 : ratBits 1 = 3 := by decide
  have h2 : ratBits 2 = 4 := by decide
  have hm := ratBits_sub_le z 1
  have hp := ratBits_sub_le z (-1)
  rw [sub_neg_eq_add, ratBits_neg] at hp
  have hw : ratBits w ≤ W := by
    have hv := ratBits_div_le (z-1) (z+1)
    dsimp [w, W]; omega
  have wden : w.den.size ≤ W+1 := Nat.size_le.mpr <| Nat.lt_log2_self.trans_le
    (Nat.pow_le_pow_right (by decide) (by have hu := hw; unfold ratBits at hu; omega))
  have pbits (j : ℕ) (hj : j ≤ 2*M+2) : ratBits (w^j) ≤ P := by
    have hj' := Nat.mul_le_mul_left W hj
    have hh := ratBits_pow_le w W j hw
    dsimp [P]; omega
  have jbits (j : ℕ) (hj : j ≤ 2*M+2) : ratBits (j : ℚ) ≤ 2*M+5 := by
    have hh := natCast_ratBits_le (e := j) (show j ≤ 2 ^ j from Nat.lt_two_pow_self.le)
    omega
  have sbits (i : ℕ) (hi : i ≤ M) : ratBits (logTruncation z i) ≤ S := by
    let s := logTruncation z i
    obtain ⟨hd,hn⟩ := logTruncation_bitSize hz hi
    change s.den.size ≤ 2*M*(2*M+w.den.size)+2*M+1 at hd
    change s.num.natAbs.size ≤ 2*M*(2*M+w.den.size)+2*M+1 at hn
    have hmono : 2*M*(2*M+w.den.size) ≤ 2*M*(2*M+W+1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hsn := log2_le_of_le_two_pow (Nat.lt_size_self s.num.natAbs).le
    have hsd := log2_le_of_le_two_pow (Nat.lt_size_self s.den).le
    change 3+s.num.natAbs.log2+s.den.log2 ≤ S
    dsimp [S]; omega
  refine ⟨hB.trans (by dsimp [H]; omega), hm.trans (by dsimp [H]; omega),
    hp.trans (by dsimp [H]; omega), hw.trans (by dsimp [H]; omega),
    fun j hj => (pbits j hj).trans (by dsimp [H]; omega),
    fun j hj => (jbits j hj).trans (by dsimp [H]; omega), ?_, ?_,
    fun i hi => (sbits i hi).trans (by dsimp [H]; omega)⟩
  · intro j hj
    have hdiv := ratBits_div_le (w^j) (j : ℚ)
    have hpow := pbits j hj; have hj' := jbits j hj
    change ratBits (w^j / (j : ℚ)) ≤ H
    dsimp [H]; omega
  · intro i hi
    have he : oddPartial w i = logTruncation z i / 2 := by simp [oddPartial, logTruncation, w]
    rw [he]
    have hdiv := ratBits_div_le (logTruncation z i) 2
    have hh := sbits i hi
    dsimp [H]; omega

end Compression
end LinearProgramming
end Optimization
end OAI
