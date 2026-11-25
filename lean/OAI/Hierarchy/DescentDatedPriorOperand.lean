import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Fixed numeric calendar for all retained raw operand arguments of an ordinary date -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup

structure Layout where
  blocks : ℕ
  nodes : ℕ
  operands : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  /-- The retained short pointer fields have `size+2` bits. -/
  size : ℕ

namespace Layout

def jobs (l : Layout) :=l.blocks*(l.nodes*l.operands)
def rows (l : Layout) :=l.hosts*chunks l.groups l.lanes
def columns (l : Layout) :=(7*l.operands)*l.nodes
def dictionary (l : Layout) :=l.nodes*2^(((l.size+2)*l.nodes)*l.lanes)
def splicePage (l : Layout) :=2^(((l.size+2)+(l.size+2))*l.lanes)
def resolverPage (l : Layout) :=2^((11*(l.size+2))*l.lanes)
def rowCap (l : Layout) :=2^Nat.clog 2 (l.rows+1)
def span (l : Layout) :=2^Nat.clog 2 l.rows

/-- Each job covers every host/group at one public block, previous node and
operand index. This numeric schedule visits unused/padded indices as well. -/
def index (l : Layout) : (Fin l.blocks×(Fin l.nodes×Fin l.operands)) ≃ Fin l.jobs :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def projected (l : Layout) (base : ℕ):=base+l.dictionary
def splice (l : Layout) (base : ℕ):=l.projected base+l.columns*l.rows+l.rowCap
def resolveBase (l : Layout) (base : ℕ):=l.splice base+4*l.splicePage+2*l.span
def output (l : Layout) (base : ℕ):=l.resolveBase base+12*l.resolverPage+2*l.rowCap
def siteWords (l : Layout) :=l.dictionary+l.columns*l.rows+l.rowCap+4*l.splicePage+2*l.span+12*l.resolverPage+3*l.rowCap

def slot (l : Layout) (floor j : ℕ):=floor+j*l.siteWords
def endAddress (l : Layout) (floor : ℕ):=floor+l.jobs*l.siteWords

def clockPer (l : Layout) :=4+10*l.dictionary+(4+l.columns*(4+28*l.rows))+
  ((4+40*l.splicePage+(4+2*(4+282*l.rows)))+(12+120*l.resolverPage+420*l.rows))
def clockBudget (l : Layout) := l.jobs*l.clockPer+4

def textPer (l : Layout) := 15*(l.dictionary+1)+(15+l.columns*(11+4*12))+
  (15*(4*l.splicePage+1)+15+2*(11+4*139)+(841+15*(12*l.resolverPage+l.rows)))
def hardwareBudget (l : Layout) :=l.jobs*l.textPer+15

theorem affine (l : Layout) (floor : ℕ) : l.endAddress floor=floor+l.endAddress 0:=by simp [endAddress]
theorem floor_le (l : Layout) (floor : ℕ) : floor≤l.endAddress floor:=Nat.le_add_right ..
theorem one_extent (l : Layout) (start : ℕ) : l.output start+l.rowCap=start+l.siteWords := by
  unfold output resolveBase splice projected siteWords;omega

theorem slot_end (l : Layout) (floor j : ℕ) : l.output (l.slot floor j)+l.rowCap=l.slot floor (j+1):=by
  rw [one_extent];simp [slot,Nat.succ_mul,Nat.add_assoc]

theorem within (l : Layout) (floor : ℕ) (j : Fin l.jobs) :
    floor≤l.slot floor j.val ∧ l.output (l.slot floor j.val)+l.rowCap≤l.endAddress floor:=by
  refine ⟨Nat.le_add_right ..,?_⟩
  rw [slot_end];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _
end Layout
end Hierarchy.DescentDatedPriorOperand

end OAI
