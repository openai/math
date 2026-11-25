import OAI.Hierarchy.DescentDatedOperandHeadShape
import OAI.Hierarchy.DescentDatedOperandPages
import OAI.Hierarchy.DescentOperandReadShape
import OAI.Hierarchy.DescentSharedLeafImage

namespace OAI
/-! # Exact public footprint of the original ordinary operand source prefix -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentHaloWalkRAM DescentSIMDLookup DescentSharedCableNames
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
set_option quotPrecheck false
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree
local notation "l" => v.resolver

def operandDepotLayout : DescentDatedOperandPages.Layout :=
  ⟨(e).oldHosts,(e).oldGroups,(e).oldLanes,(e).lanes*(e).blocks,(e).fieldBits,v.profile⟩

def operandWidth : Fin 4 → ℕ :=
  ![(e).fieldBits,(l).size+2,v.bornBook.bits,Packed.bits P]
def operandShortBits :=max (max (e).fieldBits ((l).size+2)) (max v.bornBook.bits (Packed.bits P))
def ticketReadGeometry : Geometry :=
  ⟨(l).hosts,(l).groups,(l).lanes,(l).jobs,P,(fmt).blocks,(fmt).degree,(fmt).cap,v.operandShortBits,(l).size+2⟩

theorem operandWidth_le (i : Fin 4) : v.operandWidth i≤v.operandShortBits :=by
  fin_cases i
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
  · exact (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  · exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

/-- Relative to the end of the original newborn mouth. Every term is a
public layout quantity, prior to choosing the inputs or the actual RAM. -/
def rootSourceSize :=
  let old:=DescentDatedOperandPages.lastAddress fmt v.operandDepotLayout 0
  let col:=old+(P*((fmt).degree+1))*2^Nat.clog 2 (e).oldHosts
  let broadcast:=DescentSharedLeafLookup.Public.stop col (e).oldHosts (e).groups (e).lanes (Packed.bits P)
  let rank:=broadcast+P*2^Nat.clog 2 (e).oldHosts
  let previous:=rank+(l).nodes*2^((((l).size+2)*(l).nodes)*(l).lanes)
  let mouth:=previous+(l).nodes*2^((v.bornBook.bits*(l).nodes)*(l).lanes)
  let g:=v.ticketReadGeometry
  let translate:=DescentSharedLeafLookup.Public.stop 0 (l).hosts (l).groups (l).lanes v.operandShortBits+g.stageWords 2 1 g.paths
  (((mouth+v.headTransferWords)+4*2^(v.operandShortBits*(l).lanes))+translate)+g.pipelineWords

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
