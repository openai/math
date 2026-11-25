import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentOrdinaryHeadRetileLayout

namespace OAI
/-! # The five ordinary routing inputs, grouped by their actual SIMD digit widths -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentRawCablePanel DescentHaloWalkRAM DescentSharedCableNames
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
set_option quotPrecheck false
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree
local notation "blocks_" => (e).blocks

def oldHeadCount := P*((fmt).blocks*((fmt).degree*(fmt).cap))
def anchorHeadCount := P*((fmt).blocks*((fmt).cap*3))
def rawHeadCount := P*((fmt).blocks*((fmt).cap*11))
def pathHeadCount := P*((fmt).degree+1)

/-- Only the block of an argument job participates in an original source read.
All nodes and all operand slots of that block share its returned words. -/
def wideHeads : DescentOrdinaryHeadRetile.Shape :=
  ⟨blocks_*(4*v.oldHeadCount)+(blocks_*(5*v.anchorHeadCount)+blocks_*(8*v.rawHeadCount)),
    (e).hosts,(e).groups,(e).lanes,v.resolver.lanes,(e).fieldBits⟩
def narrowHeads : DescentOrdinaryHeadRetile.Shape :=
  ⟨v.pathHeadCount+P,(e).hosts,(e).groups,(e).lanes,v.resolver.lanes,Packed.bits P⟩

def headTransferWords :=v.wideHeads.endAddress 0+v.narrowHeads.endAddress 0

abbrev HeadTriple (B «fields» choices : ℕ) := Fin B×Fin «fields»×Fin choices
def headNumber (B «fields» choices : ℕ) : HeadTriple B «fields» choices ≃ Fin (B*(«fields»*choices)) :=
  ((Equiv.refl (Fin B)).prodCongr finProdFinEquiv).trans finProdFinEquiv

abbrev WideHead := HeadTriple blocks_ 4 v.oldHeadCount ⊕
  (HeadTriple blocks_ 5 v.anchorHeadCount ⊕ HeadTriple blocks_ 8 v.rawHeadCount)
abbrev NarrowHead := Fin v.pathHeadCount ⊕ Fin P

def wideHeadNumber : v.WideHead ≃ Fin v.wideHeads.n :=
  ((headNumber ..).sumCongr (((headNumber ..).sumCongr (headNumber ..)).trans finSumFinEquiv)).trans finSumFinEquiv

def narrowHeadNumber : v.NarrowHead ≃ Fin v.narrowHeads.n := finSumFinEquiv
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
