import OAI.Computability.BorderVNP.ParseBatchVerifierKeys
import OAI.Computability.BorderVNP.StackBooleanFrame
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size

/-!
# Fixed-width numerical words and binary stack slots

The sort and arithmetic frames read most significant bits first. The stack
encoding of a natural number instead lists its bits least significant first
and ends at the last one bit. Its encoding of zero is empty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackFrame

open ParseBatchSort ParseBatchCounts
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)

private def present {w : ℕ} (j : Fin w) : Expr (Fin w) :=
  Expr.disjoin (List.ofFn fun k : Fin w =>
    if j ≤ k then .input k.rev else .const false)

private theorem present_eval {w : ℕ} (j : Fin w) (x : Fin w → Bool) :
    (present j).eval x = decide (j.val < (value x).bits.length) := by
  apply Bool.eq_iff_iff.mpr
  simp only [present, Expr.eval_disjoin_true, List.mem_ofFn, exists_exists_eq_and,
    decide_eq_true_eq, Nat.size_eq_bits_len, Nat.lt_size]
  constructor
  · rintro ⟨k,hk⟩
    by_cases hj : j ≤ k
    · have hx : (value x).testBit k.val = true := by
        simpa [hj, Expr.eval, ParseBatchVerifier.value_testBit] using hk
      have hle : 2^k.val ≤ value x := by
        by_contra! h
        simp [Nat.testBit_eq_false_of_lt h] at hx
      exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hj).trans hle
    · simp [hj, Expr.eval] at hk
  · intro hj
    have hn : value x ≠ 0 := Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hj)
    let k : Fin w := ⟨(value x).log2, (Nat.log2_lt hn).mpr (value_lt _)⟩
    have hk : j ≤ k := (Nat.le_log2 hn).mpr hj
    refine ⟨k,?_⟩
    simpa [hk, Expr.eval, ← ParseBatchVerifier.value_testBit, k] using Nat.testBit_log2 hn

private theorem present_size {w : ℕ} (j : Fin w) : (present j).size ≤ 2*w+1 := by
  apply (Expr.size_disjoin_le _ 1 ?_).trans
  · simp [Nat.mul_comm]
  · intro e he
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
    split <;> rfl

private def natSlot {w : ℕ} : Slots w → Expr (Fin w)
  | (j, none) => .not (present j)
  | (j, some false) => .and (present j) (.not (.input j.rev))
  | (j, some true) => .and (present j) (.input j.rev)

private theorem natSlot_eval {w : ℕ} (x : Fin w → Bool) (i : Slots w) :
    (natSlot i).eval x = padded w (value x).bits i := by
  obtain ⟨j,b⟩ := i
  by_cases hj : j.val < (value x).bits.length
  · have hb : (value x).bits[j.val] = x j.rev :=
      (List.getI_eq_getElem _ hj).symm.trans <|
        (Nat.testBit_eq_inth _ _).symm.trans (ParseBatchVerifier.value_testBit x j)
    cases b with
    | none => simp [natSlot, Expr.eval, present_eval, hj, padded]
    | some b => cases b <;> simp [natSlot, Expr.eval, present_eval, hj, padded, hb]
  · cases b with
    | none => simp [natSlot, Expr.eval, present_eval, hj, padded]
    | some b => cases b <;> simp [natSlot, Expr.eval, present_eval, hj, padded]

/-- Serialize a fixed-width numerical word into its padded canonical binary
stack representation, including the absent slots above its highest one bit. -/
noncomputable def natEncodeFrame (w : ℕ) : Frame (Fin w) (Slots w) :=
  (Frame.initial id).step natSlot

/-- Every stack slot carries the exact symbol or absence flag of `Nat.bits`. -/
theorem natEncodeFrame_correct {w : ℕ} (x : Fin w → Bool) :
    (natEncodeFrame w).eval x = padded w (value x).bits := by
  funext i
  rw [natEncodeFrame, Frame.step_eval]
  have hi : (Frame.initial id).eval x = x := funext fun _ => by simp
  rw [hi]
  exact natSlot_eval x i

/-- The serializer uses quadratically many Boolean gates in the word width. -/
theorem natEncodeFrame_size (w : ℕ) :
    (natEncodeFrame w).size ≤ 12*w*(w+1) := by
  have hs (i : Slots w) : (natSlot i).size ≤ 2*w+4 := by
    obtain ⟨j,b⟩ := i
    have hp := present_size j
    cases b with
    | none => simp only [natSlot, Expr.size]; omega
    | some b => cases b <;> simp only [natSlot, Expr.size] <;> omega
  apply (Frame.step_size_le (Frame.initial id) _ _ hs).trans
  simp [Slots]
  nlinarith

/-- Reverse the slot order and read its true-bit wire. This supplies the
leading zeroes of the fixed-width numerical word for free. -/
noncomputable def natDecodeFrame (w : ℕ) : Frame (Slots w) (Fin w) :=
  Frame.initial fun j => (j.rev,some true)

/-- Deserialization recovers the canonical fixed-width representative. -/
theorem natDecodeFrame_correct {w : ℕ} (a : Fin (2^w)) :
    (natDecodeFrame w).eval (padded w a.val.bits) = (numberWords w).symm a := by
  funext j
  have h := ParseBatchVerifier.value_testBit ((numberWords w).symm a) j.rev
  rw [Fin.rev_rev, value_encode, Nat.testBit_eq_inth, List.getI_eq_getElem?_getD] at h
  rw [← h, natDecodeFrame, Frame.initial_eval]
  change decide (a.val.bits[j.rev.val]? = some true) = (a.val.bits[j.rev.val]?).getD false
  cases a.val.bits[j.rev.val]? with
  | none => rfl
  | some b => cases b <;> rfl

/-- The deserializer selects existing wires and introduces zero gates. -/
theorem natDecodeFrame_size (w : ℕ) : (natDecodeFrame w).size = 0 := rfl

end StackFrame

end BorderVNP
end Computability
end OAI
