import OAI.Hierarchy.DescentResetOperandSetup
import OAI.Hierarchy.DescentResetPublicOperandBook
import OAI.Hierarchy.DescentRotorFlatFields

namespace OAI
/-! The four ROM programs for reciprocal operands share one board and one fixed ordered argument list. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup
open scoped Fin.CommRing
noncomputable section
/-- Header, per-donor coordinate pair, original endpoint packet, and the two matrix-only
suffixes. The reserved registers of the twelve-field donor record remain present in the ROM. -/
def publicOperands (D k cap n : ℕ) :=
  8+12*(2^k*(2*cap))+DescentFallbackPeriod.inputCount D (2^k) cap n k+
    ((2^k)*(2^k)+D*(D*6))

def publicMenu {n h : ℕ} (board : NonlinearExpanders.Graph n h)
    (D k cap Ht bits query lanes grainUnits args nodes packet gain multiplicity payload : ℕ) :
    DescentResetPublicOperandBook.Config where
  residual:=k
  sectors:=2^n
  maxDepth:=Ht
  privateSlots:=DescentResetCableSlots.cableCap board Ht
  fieldBits:=bits
  queryBits:=query
  lanes:=lanes
  oldDegree:=D
  oldCap:=cap
  donors:=2^k
  fineBits:=k
  batches:=grainUnits
  split:=grainUnits
  nodes:=nodes
  args:=args
  packetWidth:=packet
  gain:=gain
  multiplicity:=multiplicity
  grain:=payload

theorem public_arity {n h : ℕ} (board : NonlinearExpanders.Graph n h)
    (D k cap Ht bits query lanes grainUnits args nodes packet gain multiplicity payload : ℕ) :
    (publicMenu board D k cap Ht bits query lanes grainUnits args nodes packet gain multiplicity payload).inputs n=
      publicOperands D k cap n :=rfl

variable {n h : ℕ} (C : Chart) (board : NonlinearExpanders.Graph n h) (p : DescentResetPublicOperandBook.Config)

structure Format : Prop where
  args : C.retained.args=p.args
  nodes : C.retained.nodes=p.nodes
  rotor : C.rotorBits=p.fieldBits
  publicWidth : C.fallbackBits=p.fieldBits
  count : C.fallbackInputs=p.inputs n

namespace Format
variable {C p} (fmt : C.Format (n:=n) p)
include fmt in
theorem members : C.members=p.mouths :=congrArg₂ (·*·) fmt.args fmt.nodes

def privateColumn (width : ℕ) (x : Fin 4→Cell C.rotorBits) (f : Fin 8) (j : Fin C.members) : Cell width :=
  let q : Fin p.args×Fin p.nodes:=finProdFinEquiv.symm (j.cast fmt.members)
  let reg : Fin 4→Cell p.fieldBits:=fun i=>(x i).cast (congrArg (2^·) fmt.rotor)
  p.rotor.flatReg board p.multiplicity p.grain p.split q.2.val q.1.val f reg

def publicColumn (width : ℕ) (x : Fin C.fallbackInputs→Cell C.fallbackBits)
    (f : Option (Fin 7)) (j : Fin C.members) : Cell width :=
  let reg : p.Data n:=fun i=>(x (i.cast fmt.count.symm)).cast (congrArg (2^·) fmt.publicWidth)
  p.column board width f (j.cast fmt.members) reg

/-- The query uses the addressed oriented edge, and the seven retained fields
use the same node and argument as the query. -/
def laws : C.Laws where
  rotorQuery j x:=fmt.privateColumn board C.queryBits x 0 j
  rotorFields j x:=
    let t : Fin 7×Fin C.members:=finProdFinEquiv.symm j
    fmt.privateColumn board C.fieldBits x t.1.succ t.2
  fallbackQuery j x:=fmt.publicColumn board C.queryBits x none j
  fallbackFields j x:=
    let t : Fin 7×Fin C.members:=finProdFinEquiv.symm j
    fmt.publicColumn board C.fieldBits x (some t.1) t.2

theorem «fields» (f : Fin 7) (j : Fin C.members) (x : Fin 4→Cell C.rotorBits)
    (y : Fin C.fallbackInputs→Cell C.fallbackBits) :
    (fmt.laws board).rotorFields (finProdFinEquiv (f,j)) x=fmt.privateColumn board C.fieldBits x f.succ j ∧
    (fmt.laws board).fallbackFields (finProdFinEquiv (f,j)) y=fmt.publicColumn board C.fieldBits y (some f) j :=by
  simp only [laws, Equiv.symm_apply_apply, and_self]

end Format
end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
