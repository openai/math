import OAI.Hierarchy.DescentSelectedMatchBoard

namespace OAI
/-! The native depot fields of a selected matching board. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentPacking.PackedMatch
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1100000
attribute [local irreducible] Stage.nativeParts topologyWords Gather.flat terrain spread
  pairNumber slabPacking Stage.slot
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "J" => (S).groupCount v.age
local notation "H" => v.area.H
local notation "native" => v.prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
local notation "grp" => Equiv.refl (Fin J)
local notation "rr" => BitDescription.scannedRows v.nonnegative T
local notation "fmt" => v.ticket.depotShape v.short
variable (oldFit:Fintype.card v.prior.V≤v.area.H) (R:Fin v.area.H→Fin v.prior.placement.degree→Option (Fin v.area.H))
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected:(v.prior.placement.stage.result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

namespace SelectedBoard
variable {v oldFit R selected m parts} (B:v.SelectedBoard oldFit R selected m parts)
def material (h:Fin H)(g:Fin J):DepotRAM.Parts fmt:=
  Stage.nativeParts (short:=v.short) («H»:=H) («G»:=J) A native S v.prior.valid rank B.win grp hosts B.live v.profile B.births B.issued R (A).hub lay
    (donorNameBits v.stage.k v.stage.Δ) h g
end SelectedBoard

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
