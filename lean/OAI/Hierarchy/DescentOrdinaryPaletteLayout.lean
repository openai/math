import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.DescentOrdinaryPaletteRead
import OAI.Hierarchy.DescentOrdinaryOriginReshape
import OAI.Hierarchy.DescentOrdinaryRoleRetile
import OAI.Hierarchy.DescentOrdinaryRefsShape
import OAI.Hierarchy.DescentScalarHaloPortROM

namespace OAI
/-! The absolute ordinary primitive archive allocated after the predecessor and newborn books. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint
open ProtocolRAM DescentSIMDLookup DescentHaloWalkRAM
noncomputable section
structure Layout where
  hosts : ℕ
  degree : ℕ
  k : ℕ
  capacity : ℕ
  lows : ℕ
  groups : ℕ
  oldNodes : ℕ
  newNodes : ℕ
  primitiveBits : ℕ
  originBits : ℕ
  priorLanes : ℕ
  birthLanes : ℕ
  originLanes : ℕ
  workLanes : ℕ
  nextLanes : ℕ

namespace Layout
variable (L : Layout)
def blocks:=2^L.k
def oldGroups:=L.groups*L.blocks
def oldWork:=L.workLanes*L.blocks
def successors:=L.hosts*L.lows
def fields:=L.blocks*L.capacity*6
def ports:=breadth L.degree
def candidates:=L.ports*L.blocks*(L.oldNodes+L.capacity*6)
def prior : DescentOrdinaryRoleRetile.Layout :=
  ⟨L.blocks,L.hosts,L.oldGroups,L.priorLanes,L.oldWork,L.primitiveBits*L.oldNodes⟩
def births : DescentOrdinaryRoleRetile.Layout :=
  ⟨L.fields,L.hosts,L.oldGroups,L.birthLanes,L.oldWork,L.primitiveBits⟩
def origins : DescentOrdinaryRoleRetile.Layout :=
  ⟨L.blocks,L.successors,L.groups,L.originLanes,L.workLanes,L.originBits*L.newNodes⟩
def references (base : ℕ) : DescentOrdinaryRefsROM.Chart :=
  ⟨base,L.degree,L.k,L.oldNodes,L.newNodes,L.capacity,L.primitiveBits,0,0,L.oldWork⟩
def spread : DescentOrdinaryOriginReshape.Layout :=
  ⟨L.hosts,L.lows,L.groups,L.blocks,L.primitiveBits*L.candidates,L.workLanes⟩
def join : Shape :=
  ⟨L.candidates,L.newNodes,L.originBits,L.primitiveBits,L.blocks,L.successors,L.groups,L.workLanes⟩
def durable : DescentOrdinaryRoleRetile.Layout :=
  ⟨L.blocks,L.successors,L.groups,L.workLanes,L.nextLanes,L.primitiveBits*L.newNodes⟩

def birthStart (base : ℕ) := L.prior.roof base
def originStart (base : ℕ) := L.births.roof (L.birthStart base)
def portStart (base : ℕ) := L.origins.roof (L.originStart base)
def bookStart (base : ℕ) := DescentScalarHaloPortROM.stop L.hosts L.oldGroups L.oldWork L.ports (L.portStart base)
def spreadStart (base : ℕ) := (L.references (L.bookStart base)).endAddress
def joinStart (base : ℕ) := L.spread.finish (L.spreadStart base)
def durableStart (base : ℕ) := L.join.roof (L.joinStart base)
def roof (base : ℕ) := L.durable.roof (L.durableStart base)
def bank (base : ℕ) (x : Fin L.blocks) :=L.durable.bank (L.durableStart base) x
def bornIndex (x : Fin L.blocks) (t : Fin L.capacity) (party : Fin 6) : Fin L.fields :=
  finProdFinEquiv (finProdFinEquiv (x,t),party)

structure Inputs where
  previous : Fin L.blocks→Bank
  newborn : Fin L.fields→Bank
  origin : Fin L.blocks→Bank
  halo : Bank

theorem translated (base : ℕ) : L.roof base=base+L.roof 0:=by
  simp only [roof,durableStart,joinStart,spreadStart,bookStart,portStart,originStart,birthStart,
    DescentOrdinaryRoleRetile.Layout.roof,DescentOrdinaryRoleRetile.Layout.output,
    DescentSIMDLookup.Overlap.dest,DescentSIMDLookup.Overlap.dictBase,Shape.roof,Shape.output,
    DescentOrdinaryOriginReshape.Layout.finish,DescentOrdinaryOriginReshape.Layout.out,
    DescentScalarBookReshape.output,DescentOrdinaryOriginReshape.Layout.transpose,
    DescentOrdinaryOriginReshape.Layout.raw,ProtocolRAM.Bank.size,
    DescentOrdinaryRefsROM.Chart.endAddress,DescentOrdinaryRefsROM.Chart.tableBase,
    DescentOrdinaryRefsROM.Chart.digitSize,DescentOrdinaryRefsROM.Chart.digitBits,
    DescentOrdinaryRefsROM.Chart.tableSize,DescentOrdinaryRefsROM.Chart.count,
    DescentOrdinaryRefsROM.Chart.width,DescentOrdinaryRefsROM.Chart.keyBits,
    DescentOrdinaryRefsROM.Chart.actors,DescentOrdinaryRefsROM.Chart.nodes,DescentOrdinaryRefsROM.Chart.donors,
    DescentScalarHaloPortROM.stop,references,Nat.zero_add,Nat.add_assoc]

end Layout
end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint

end OAI
