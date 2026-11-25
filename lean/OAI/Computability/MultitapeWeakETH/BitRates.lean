import OAI.Computability.MultitapeWeakETH.EntropyPrice
import Mathlib.Data.Nat.Bitwise

/-! # The individual and total rates of the retained payload bits -/

namespace OAI.Computability.MultitapeWeakETH

open Finset MatrixMultiplication.Foundation
open scoped BigOperators Classical
noncomputable section

variable {A : Type} [Fintype A] {L : ℕ}

def payloadLabels (word : A → Fin (2^L)) (i : ℕ) (x : A) : Bool := (word x).val.testBit i

omit [Fintype A] in
private theorem bit_eq_of_record (labels : ℕ → A → Bool) (depth : ℕ) (a b : A)
    (equal : labelRecordOf labels depth a = labelRecordOf labels depth b) :
    ∀ i < depth, labels i a = labels i b := by
  induction depth with
  | zero => simp
  | succ n ih =>
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
    · exact ih (congrArg Prod.fst equal) i h
    · exact congrArg Prod.snd equal

omit [Fintype A] in
theorem payload_separates (word : A → Fin (2^L)) (inj : Function.Injective word) :
    Function.Injective (labelRecordOf (payloadLabels word) L) := by
  intro a b h
  apply inj
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < L
  · exact bit_eq_of_record _ _ _ _ h i hi
  · have bound : 2^L ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt ((word a).isLt.trans_le bound),
      Nat.testBit_eq_false_of_lt ((word b).isLt.trans_le bound)]

def bitRate (p : FiniteLaw A) (labels : ℕ → A → Bool) (depth : ℕ) (i : Fin depth) : ℝ :=
  (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy i / Real.log 2

theorem bitRate_range (p : FiniteLaw A) (labels : ℕ → A → Bool) (depth : ℕ) (i : Fin depth) :
    0 ≤ bitRate p labels depth i ∧ bitRate p labels depth i ≤ 1 := by
  unfold bitRate
  rw [FiniteLabelHierarchy.ofLawLabels_refinementEntropy_eq _ _ _ _ i.isLt]
  let pre := p.map (labelRecordOf labels i)
  let q r := (p.conditional (labelRecordOf labels i) r).map (labels i)
  have hi (r) : finiteEntropy (q r).mass ≤ Real.log 2 := by
    simpa using (q r).entropy_le_log_card
  constructor
  · exact div_nonneg (sum_nonneg fun r _ => mul_nonneg (pre.nonneg r) (q r).entropy_nonneg) (by positivity)
  · apply (div_le_one (by positivity : 0 < Real.log 2)).mpr
    calc
      _ ≤ ∑ r, pre.mass r * Real.log 2 := sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hi r) (pre.nonneg r)
      _ = _ := by rw [← sum_mul,pre.total,one_mul]

theorem sum_bitRate [Nonempty A] (word : A → Fin (2^L)) (inj : Function.Injective word) :
    ∑ i, bitRate (FiniteLaw.uniform A) (payloadLabels word) L i = Real.logb 2 (Fintype.card A) := by
  simp only [bitRate,← sum_div,Real.logb]
  rw [Fin.sum_univ_eq_sum_range,FiniteLabelHierarchy.ofLawLabels_refinementEntropy_sum _ _ _ (payload_separates word inj),
    FiniteLaw.uniform_entropy]

end
end OAI.Computability.MultitapeWeakETH
