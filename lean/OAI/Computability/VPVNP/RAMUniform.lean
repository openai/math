import OAI.Computability.VPVNP.RAMProgram

/-!
# A single burst instruction table at different word widths

The public parameters and the machine word width depend on the input length.
The instruction destinations, operand registers, and literal constants of a
fixed program do not. A table in the finite literal format can be instantiated
at every width. Increasing the width past the literal width preserves each
constant's natural value.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM

variable {p r k v w : ℕ}

/-- Resize just the immediate constants of an instruction. No opcode, register,
public-data location, jump target, or branch order is changed. -/
def Instr.resize (w : ℕ) : Instr v p r k → Instr w p r k
  | .constant dst value next => .constant dst (Fin.ofNat _ value.val) next
  | .publicWord dst i next => .publicWord dst i next
  | .stateWord dst next => .stateWord dst next
  | .copy dst src next => .copy dst src next
  | .binary op dst x y next => .binary op dst x y next
  | .loadPrivate dst a next => .loadPrivate dst a next
  | .storePrivate a src next => .storePrivate a src next
  | .jumpEq x y yes no => .jumpEq x y yes no
  | .jumpLt x y yes no => .jumpLt x y yes no
  | .choose yes no => .choose yes no
  | .readExternal dst a next => .readExternal dst a next
  | .writeExternal a src next => .writeExternal a src next
  | .returnState src => .returnState src
  | .accept => .accept
  | .reject => .reject

theorem resize_literal (hv : v ≤ w) (a : Word v) :
    (Fin.ofNat (2^w) a.val).val = a.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) hv))

/-- The finite, length-independent part of a call program. -/
structure Template (p r k : ℕ) where
  /-- Bit width in which the fixed instruction table stores its literal constants. -/
  literalWidth : ℕ
  /-- First instruction address of this table, shared by all word-width instantiations. -/
  entry : Fin p
  /-- Instruction stored at each bounded program counter, with constants encoded at the
  template's literal width. -/
  code : Fin p → Instr literalWidth p r k

/-- Resize the table's literal constants to the runtime word width and install the supplied
public operands. -/
def Template.instantiate (t : Template p r k) (w : ℕ) (pub : Fin k → Word w) : Machine w p r k where
  entry := t.entry
  code i := (t.code i).resize w
  publicData := pub

theorem Template.constant_value (t : Template p r k) (w : ℕ) (pub : Fin k → Word w)
    (i : Fin p) (dst : Fin r) (a : Word t.literalWidth) (next : Fin p)
    (h : t.code i = .constant dst a next) (hw : t.literalWidth ≤ w) :
    (t.instantiate w pub).code i = .constant dst
      ⟨a.val, Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) hw)⟩ next := by
  simp [instantiate, h, Instr.resize, Fin.ext_iff, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) hw))]

end BurstRAM.PrivateRAM

end VPVNP
end Computability
end OAI
