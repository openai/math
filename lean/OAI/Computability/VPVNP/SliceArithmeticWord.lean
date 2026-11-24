import OAI.Computability.VPVNP.RAMTapeWordISAStage
import Mathlib.Data.Nat.Log

/-!
# Prime-field coefficient arithmetic on bit stacks

The advice supplies the modulus and the canonical coefficients in registers.
A fixed pair of word instructions computes each operation. The first instruction
forms an ordinary integer sum, product or difference at a width large enough
to retain it. The second reduces this word modulo the advised modulus.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.Word

open BurstRAM PrivateRAM RAMTape ISA

/-- Word width sufficient for a sum or product of two canonical residues and
the modulus itself. The routine also accepts any wider register bank. -/
def workingWidth (p : ℕ) := 2 * Nat.clog 2 p + 1

theorem workingWidth_capacity {p w : ℕ} (h : workingWidth p ≤ w) :
    2 * p ^ 2 ≤ 2 ^ w := by
  have hp := Nat.le_pow_clog (by decide : 1 < 2) p
  calc
    2 * p ^ 2 ≤ 2 * (2 ^ Nat.clog 2 p) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp _)
    _ = 2 ^ workingWidth p := by
      rw [workingWidth, mul_comm 2 (Nat.clog _ _), ← pow_mul, pow_succ' 2 (Nat.clog 2 p * 2)]
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) h

/-- Embed a canonical residue in a register. -/
def limb {p : ℕ} (w : ℕ) (a : Fin p) : BurstRAM.Word w := Fin.ofNat _ a.val

theorem modulus_lt {p w : ℕ} [NeZero p] (h : workingWidth p ≤ w) : p < 2 ^ w := by
  have hp := NeZero.pos p
  have hc := workingWidth_capacity h
  nlinarith

@[simp] theorem limb_val {p w : ℕ} [NeZero p] (h : workingWidth p ≤ w) (a : Fin p) :
    (limb w a).val = a.val := Nat.mod_eq_of_lt (a.isLt.trans (modulus_lt h))

/-- The residue operations supported by the fixed word routine for field arithmetic. -/
inductive Op where
  | add | mul | neg
  deriving DecidableEq

/-- Evaluate the chosen operation modulo `p`, using only the first operand for negation. -/
def Op.eval {p : ℕ} : Op → Fin p → Fin p → Fin p
  | .add, x, y => x + y
  | .mul, x, y => x * y
  | .neg, x, _ => -x

private def Op.first : Op → BinaryOp
  | .add => .add
  | .mul => .mul
  | .neg => .sub

private def Op.inputs {α : Type*} (op : Op) (x y modulus : α) : α × α :=
  match op with
  | .add | .mul => (x, y)
  | .neg => (modulus, x)

/-- Both the opcode table and the port assignment are independent of the
prime and of the word width. The destination is reused as the intermediate. -/
def routine {r k : ℕ} (op : Op) (dst lhs rhs modulusReg : Fin r) : FiniteRoutine (Port r k) :=
  let args := op.inputs lhs rhs modulusReg
  (binary op.first dst args.1 args.2).followedBy (binary .mod dst dst modulusReg)

private theorem reduced {p w : ℕ} [NeZero p] (hw : workingWidth p ≤ w)
    (op : Op) (x y : Fin p) (a b m : BurstRAM.Word w)
    (ha : a.val = x.val) (hb : b.val = y.val) (hm : m.val = p) :
    let args := op.inputs a b m
    BinaryOp.mod.eval (op.first.eval args.1 args.2) m = limb w (op.eval x y) := by
  have hcap := workingWidth_capacity hw
  have hp := NeZero.pos p
  have hpx := x.isLt
  have hpy := y.isLt
  have hsq : p ≤ p ^ 2 := by nlinarith
  have hadd : x.val + y.val < 2 ^ w := by omega
  have hmul : x.val * y.val < 2 ^ w :=
    (Nat.mul_lt_mul_of_lt_of_le hpx hpy.le hp).trans_le (by nlinarith)
  have hsub : a ≤ m := by change a.val ≤ m.val; omega
  cases op with
  | add =>
    simp [Op.inputs, Op.first, Op.eval, BinaryOp.eval, limb, ha, hb, hm, Fin.val_add, Nat.mod_eq_of_lt hadd]
  | mul =>
    simp [Op.inputs, Op.first, Op.eval, BinaryOp.eval, limb, ha, hb, hm, Fin.val_mul, Nat.mod_eq_of_lt hmul]
  | neg =>
    simp [Op.inputs, Op.first, Op.eval, BinaryOp.eval, limb, Fin.sub_val_of_le hsub, ha, hm, Fin.neg_def]

/-- A clean architectural bank returns with only the destination register
updated. Input registers can alias the destination, since the first
instruction stages its operands before writeback. -/
theorem routine_runs {p r k w : ℕ} [NeZero p] (hw : workingWidth p ≤ w)
    (op : Op) (dst lhs rhs modulusReg : Fin r) (hd : modulusReg ≠ dst)
    (pub : Fin k → BurstRAM.Word w) (persistent : BurstRAM.Word w)
    (reg : Fin r → BurstRAM.Word w) (log : WriteLog w) (x y : Fin p)
    (hx : (reg lhs).val = x.val) (hy : (reg rhs).val = y.val) (hm : (reg modulusReg).val = p) :
    ∃ t ≤ 200 * (w + 1) ^ 2, (routine op dst lhs rhs modulusReg).Runs t
      (bank pub persistent reg log)
      (bank pub persistent (Function.update reg dst (limb w (op.eval x y))) log) := by
  let args := op.inputs lhs rhs modulusReg
  let raw := op.first.eval (reg args.1) (reg args.2)
  let middle := Function.update reg dst raw
  obtain ⟨t₁, h₁, run₁⟩ := binary_runs op.first dst args.1 args.2 pub persistent reg log
  obtain ⟨t₂, h₂, run₂⟩ := binary_runs .mod dst dst modulusReg pub persistent middle log
  have hresult : BinaryOp.mod.eval (middle dst) (middle modulusReg) = limb w (op.eval x y) := by
    simp only [middle, Function.update_self, Function.update_of_ne hd]
    have h := reduced hw op x y (reg lhs) (reg rhs) (reg modulusReg) hx hy hm
    cases op <;> exact h
  rw [hresult, show Function.update middle dst (limb w (op.eval x y)) =
      Function.update reg dst (limb w (op.eval x y)) from Function.update_idem ..] at run₂
  exact ⟨t₁ + t₂, by omega, run₁.followedBy run₂⟩

end SliceArithmetic.Word

end VPVNP
end Computability
end OAI
