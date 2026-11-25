import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # The label chooser's sparse incident-cable lists

The first word of a node is a one-based link (zero terminates a list). Its remaining
three words store the orientation relative to this cell, the other cell and the width.
Both incident lists may refer to one cable, but each fixing step scans only its own list.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM

/-- Oriented incident cable, viewed from the cell being fixed. -/
structure Incident where
  /-- Zero for an outgoing cable, one for an incoming cable. -/
  dir : ℕ
  /-- Ordinal of the opposite cell. -/
  other : ℕ
  /-- Number of bit wires carried by this cable. -/
  width : ℕ
deriving DecidableEq

/-- Offset of the first word at a one-based node pointer. -/
def nodeAddr (base ptr : ℕ) := base + 4 * (ptr-1)

/-- The actual links and three payload words encode this list in memory. -/
inductive Chain (m : ℕ → ℕ) (base : ℕ) : ℕ → List Incident → Prop where
  | nil : Chain m base 0 []
  | cons {ptr : ℕ} {e : Incident} {es : List Incident}
      (live : 0 < ptr) (dir : m (nodeAddr base ptr+1) = e.dir)
      (other : m (nodeAddr base ptr+2) = e.other)
      (width : m (nodeAddr base ptr+3) = e.width)
      (tail : Chain m base (m (nodeAddr base ptr)) es) : Chain m base ptr (e :: es)

/-- Registers 24 and 25 are the linked-list cursor and address scratch. Each row
loads its successor before fetching its orientation, opposite endpoint and width. -/
def readNode : Code := .block [
  .binary .sub 25 24 20, .binary .mul 25 30 25, .binary .add 25 29 25,
  .load 24 25, .binary .add 25 25 20, .load 5 25,
  .binary .add 25 25 20, .load 6 25, .binary .add 25 25 20, .load 8 25,
  .binary .add 25 21 6, .load 7 25]

/-- Registers whose contents can be replaced in a row load. -/
def rowScratch (r : Reg) : Bool := [5,6,7,8,24,25].contains r

/-- Preservation for unsigned straight-line computations, including writes to memory. -/
theorem keeps_eval {r : Reg} (c : Code) (pub : Arg → ℕ) (z : NatState) (h : c.keeps r = true) :
    (c.fixedEval pub z).reg r = z.reg r := by
  induction c generalizing z with
  | seq a b iha ihb =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    exact (ihb _ hb).trans (iha _ ha)
  | ifEq x y a b iha ihb | ifLt x y a b iha ihb =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    simp only [Code.fixedEval]
    split <;> first | exact iha _ ha | exact ihb _ hb
  | constant | copy | binary | publicWord | load =>
    exact Function.update_of_ne (of_decide_eq_true h) ..
  | _ => rfl

/-- Reading one row returns its successor and all four cable inputs; the opposite
label is fetched at its public cell index. The row itself is read-only. -/
theorem readNode_eval (pub : Arg → ℕ) (z : NatState)
    (one : z.reg 20 = 1) (four : z.reg 30 = 4) :
    let a := nodeAddr (z.reg 29) (z.reg 24)
    let out := readNode.fixedEval pub z
    out.reg 24 = z.mem a ∧ out.reg 5 = z.mem (a+1) ∧ out.reg 6 = z.mem (a+2) ∧
      out.reg 8 = z.mem (a+3) ∧ out.reg 7 = z.mem (z.reg 21 + z.mem (a+2)) ∧
      out.mem = z.mem ∧ ∀ r, rowScratch r = false → out.reg r = z.reg r := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,rfl,?_⟩
  case refine_6 =>
    intro r hr
    exact keeps_eval _ _ _ ((show ∀ i, rowScratch i = false → readNode.keeps i = true by decide) r hr)
  all_goals try simp [readNode, Code.block, Code.fixedEval, Code.evalNat, addressOp, one, four,
    Function.update, nodeAddr, Nat.add_assoc]

/-- The link address, payload and label address suffice to prevent every overflow
and underflow in a physical row load. -/
theorem readNode_safe (w : ℕ) (pub : Arg → ℕ) (z : NatState)
    (one : z.reg 20 = 1) (four : z.reg 30 = 4) (live : 0 < z.reg 24)
    (row : nodeAddr (z.reg 29) (z.reg 24) + 3 < 2^w)
    (label : z.reg 21 + z.mem (nodeAddr (z.reg 29) (z.reg 24) + 2) < 2^w) :
    readNode.fixedSafe w pub z := by
  simp [readNode, Code.block, Code.fixedSafe, Code.fixedEval, Code.safeReadOnly,
    Code.evalNat, addressOp, addressOpFits, one, four, Function.update, Nat.add_assoc]
  simp only [nodeAddr,Nat.add_assoc] at row label
  omega

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
