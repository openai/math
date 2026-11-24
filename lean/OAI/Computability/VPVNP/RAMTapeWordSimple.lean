import OAI.Computability.VPVNP.RAMTapeWordScan
import OAI.Computability.VPVNP.RAMProgram

/-!
# Arithmetic and logical RAM opcodes in the finite scan control

Addition and subtraction discard the final overflow bit. Parallel Boolean
operations use a dummy flag. The same subtraction run retains the unsigned
comparison result in its final state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord

open RAMTape BurstRAM BurstRAM.PrivateRAM

/-- RAM operations computable by scanning pairs of corresponding bits with a single Boolean
carry or borrow. -/
inductive ScanOp where
  | add | sub | bitAnd | bitOr | bitXor
  deriving DecidableEq

/-- Identify the bit-scan operation with the corresponding binary RAM opcode. -/
def ScanOp.opcode : ScanOp → BinaryOp
  | .add => .add
  | .sub => .sub
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .bitXor => .bitXor

/-- Compute one output bit and the next carry or borrow. Bitwise logical operations compute the
output without a carry. -/
def ScanOp.step : ScanOp → Bool → Bool → Bool → Bool × Bool
  | .add => addBit
  | .sub => subBit
  | .bitAnd => fun _ a b => (a && b, false)
  | .bitOr => fun _ a b => (a || b, false)
  | .bitXor => fun _ a b => (a ^^ b, false)

private theorem addScan_wordBits {w : ℕ} (a b : Word w) :
    (addScan false (wordBits a) (wordBits b)).1 = wordBits (a + b) := by
  have hlen : (wordBits a).length = (wordBits b).length := by simp
  have hr := length_addScan (c := false) hlen
  simp only [length_wordBits] at hr
  have hv := addScan_spec (c := false) hlen
  simp only [length_wordBits, value_wordBits, Bool.toNat_false, Nat.add_zero] at hv
  have hlo := value_lt (addScan false (wordBits a) (wordBits b)).1
  rw [hr] at hlo
  apply eq_of_length_value (by simpa using hr)
  rw [value_wordBits, Fin.val_add, ← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]

private theorem subScan_wordBits {w : ℕ} (a b : Word w) :
    (subScan false (wordBits a) (wordBits b)).1 = wordBits (a - b) := by
  have hlen : (wordBits a).length = (wordBits b).length := by simp
  have hr := length_subScan (c := false) hlen
  simp only [length_wordBits] at hr
  have hv := subScan_spec (c := false) hlen
  simp only [length_wordBits, value_wordBits, Bool.toNat_false, Nat.add_zero] at hv
  have hlo := value_lt (subScan false (wordBits a) (wordBits b)).1
  rw [hr] at hlo
  apply eq_of_length_value (by simpa using hr)
  rw [value_wordBits, Fin.val_sub]
  have hb := b.isLt
  cases h : (subScan false (wordBits a) (wordBits b)).2
  · simp only [h, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
    have he : 2^w - b.val + a.val = value (subScan false (wordBits a) (wordBits b)).1 + 2^w := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hlo]
  · simp only [h, Bool.toNat_true, Nat.mul_one] at hv
    have he : 2^w - b.val + a.val = value (subScan false (wordBits a) (wordBits b)).1 := by omega
    rw [he, Nat.mod_eq_of_lt hlo]

private theorem logic_wordBits {w : ℕ} (op : Bool → Bool → Bool) (hzero : op false false = false)
    (a b : Word w) : (logicScan op (wordBits a) (wordBits b)).1 =
      wordBits (Fin.ofNat (2^w) (Nat.bitwise op a.val b.val)) := by
  have hlen : (wordBits a).length = (wordBits b).length := by simp
  have hr := length_scan (fun _ x y => (op x y, false)) false _ _ hlen
  have hs := logicScan_spec hzero hlen
  have hlo := value_lt (logicScan op (wordBits a) (wordBits b)).1
  change (logicScan op (wordBits a) (wordBits b)).1.length = _ at hr
  rw [hr, length_wordBits] at hlo
  simp only [value_wordBits] at hs
  apply eq_of_length_value (by simpa using hr)
  rw [value_wordBits, Fin.val_ofNat, ← hs, Nat.mod_eq_of_lt hlo]

theorem ScanOp.result_wordBits {w : ℕ} (op : ScanOp) (a b : Word w) :
    (scan op.step false (wordBits a) (wordBits b)).1 = wordBits (op.opcode.eval a b) := by
  cases op with
  | add => exact addScan_wordBits ..
  | sub => exact subScan_wordBits ..
  | bitAnd => exact logic_wordBits (· && ·) rfl a b
  | bitOr => exact logic_wordBits (· || ·) rfl a b
  | bitXor => exact logic_wordBits (· ^^ ·) rfl a b

/-- Literal bit-stack executions of all five linear-time binary opcodes. -/
theorem ScanOp.word_run {w : ℕ} (op : ScanOp) (a b : Word w) :
    StackRuns (scanCode op.step) (5 * w + 2) (.left false) (scanStacks (wordBits a) (wordBits b) [] [])
      (.done (scan op.step false (wordBits a) (wordBits b)).2)
      (scanStacks [] [] [] (wordBits (op.opcode.eval a b))) := by
  simpa only [length_wordBits, op.result_wordBits, List.append_nil] using
    scanRuns op.step false (wordBits a) (wordBits b) [] (by simp)

/-- Unsigned comparison of the operands can branch directly on the final
borrow of the subtraction scan. -/
theorem subScan_borrow {c : Bool} {x y : List Bool} (hlen : x.length = y.length) :
    (subScan c x y).2 = true ↔ value x < value y + c.toNat := by
  have hv := subScan_spec (c := c) hlen
  have hz := value_lt (subScan c x y).1
  rw [length_subScan hlen] at hz
  cases h : (subScan c x y).2 <;> simp only [h, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
    Nat.mul_one, Nat.add_zero] at hv <;> simp <;> omega

end TapeWord

end VPVNP
end Computability
end OAI
