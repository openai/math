import OAI.Hierarchy.DescentPreviousOperandLayout

namespace OAI
/-! # Final ordinary operand books in the successor node order -/
namespace Hierarchy.DescentOrdinaryFinal
open DescentSIMDLookup DescentOperandStateBanks DescentDatedPriorOperand ProtocolRAM
noncomputable section

structure Chart where
  layout : DescentDatedPriorOperand.Layout
  roleBits : ℕ
  arityBits : ℕ

namespace Chart
variable (B : Chart)
def field := B.layout.size+2
def keys := B.layout.nodes*B.layout.operands
def inputs := 3+B.keys
def outputs :=7*B.layout.operands
def scalarWidth :=max (B.roleBits*B.layout.nodes) (max (B.arityBits*B.layout.nodes)
  (max (B.field*B.layout.nodes) ((B.layout.size+4)*5)))
def castWords :=4*(2*2^(B.scalarWidth*B.layout.lanes))
def castEnd (floor : ℕ) :=floor+B.castWords
def tableWords :=(B.inputs+B.outputs)*(2*2^((B.scalarWidth*B.inputs+B.scalarWidth)*B.layout.lanes))
def out (floor : ℕ) :=B.castEnd floor+B.tableWords
def rows :=B.layout.rows
def passes :=B.outputs*B.layout.blocks
def endAddress (floor : ℕ) := B.out floor+B.passes*B.rows+2^Nat.clog 2 (B.rows+1)
def bank (floor : ℕ) (x : Fin B.layout.blocks) (p : Pages B.layout.operands) :=
  DescentDatedPriorOperand.previousBank B.layout (B.out floor) x p

theorem affine (floor : ℕ) : B.endAddress floor=floor+B.endAddress 0:=by
  simp [endAddress,out,castEnd,Nat.add_assoc]

theorem order (floor : ℕ) : floor≤B.castEnd floor ∧ B.castEnd floor≤B.out floor ∧
    B.out floor+B.passes*B.rows≤B.endAddress floor :=
  ⟨Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩

end Chart
end
end Hierarchy.DescentOrdinaryFinal

end OAI
