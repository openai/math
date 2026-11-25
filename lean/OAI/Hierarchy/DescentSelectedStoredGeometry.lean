import OAI.Hierarchy.DescentSelectedAcquiredRows

namespace OAI
/-! The real selected board's actor routes restricted to prior hosts, including all padded rows. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
noncomputable section
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys" => v.withIssuedSigned
local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "D" => (A).degree
local notation "r" => 2^v.k
local notation "J" => (S).groupCount v.age
local notation "M" => (phys).material.oldLanes
local notation "H" => v.area.H
local notation "ss" => (phys).signed
local notation "native" => v.prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
local notation "grp" => Equiv.refl (Fin J)
local notation "peers" => rotor A rank
local notation "home" => scanHomeAt v.nonnegative T
local notation "color" => scanColorAt v.nonnegative T
local notation "addr" => nativeAddress v.nonnegative T
local notation "rr" => BitDescription.scannedRows v.nonnegative T
local notation "K" => 2^(v.k+1)
local notation "s" => shape r D (2*(A).cap) v.profile
local notation "traffic" => nativeTraffic v.world.graph v.world.core home
local notation "fmt" => v.ticket.depotShape v.short

open DescentOrdinaryVenueIngress DescentScalarVenueMask DescentPackedColony DescentSortedHaloRaster DescentGroupPeerOrder
variable (oldFit:Fintype.card v.prior.V≤H)
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
local notation "liveRoster" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding))
variable (selected:((T).result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)


open DescentLocalArchiveOrder DescentScalarVenueMask
local notation "slots" => DescentOrdinaryVenueReturn.shapeSlots D
local notation "cut" => v.ticket
local notation "rows" => BitDescription.scannedRows v.nonnegative v.stage
local notation "feeLayout" => bestLayout (branchWidth G (fun _ : (rows).pairs=>v.stage.z) ((rows).profile v.choice))
local notation "site" => GadgetNetwork.newSite v.world.graph (rows).pick feeLayout (rows).pack
local notation "owners" => (activeChart cut).key v.nonnegative v.stage v.choice
local notation "moves" => rotor A rank



variable (rho:Fin H→Fin D→Option (Fin H)) (source:rho=liveRoster)
  (board:v.SelectedBoard oldFit rho selected m parts)
local notation "active_" => Prepare.actors A (Function.Embedding.refl _) hosts
local notation "routes_" => fun x j h g=>DepotRAM.ActorInputs.token fmt v.profile slots (2^(v.k+1)*slots)
  (board.material h g) (active_ h g) (x,j)
local notation "stored_" => fun x j (h:Fin (Fintype.card v.prior.V)) g=>routes_ x j (h.castLE oldFit) g

include source in
theorem selected_stored_geometry (choiceEq : HEq selected v.choice) :
    Descriptors slots v.k (A).pos (A).block (ticketParent (he:=v.nonnegative) («T»:=v.stage))
      (ticketSlot (c:=v.choice) cut) (owners∘site) v.prior.vertex (Function.Embedding.refl _) moves stored_ ∧
    (∀x j (h:Fin H) g,Fintype.card v.prior.V≤h.val→ routes_ x j h g=none) ∧
    ∀h,Census.hub A hosts (h.castLE oldFit)=Census.hub A v.prior.vertex h:=by
  exact v.selected_material_rows oldFit selected m parts rho source board choiceEq

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
