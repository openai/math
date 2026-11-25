import OAI.Hierarchy.DescentSelectedMatchBoard
import OAI.Hierarchy.DescentOrdinaryVenueIngressPrior
import OAI.Hierarchy.DescentFundedClipChoice

namespace OAI
/-! # Issue the ordinary actor raster from the very donor board used for both signed ends -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 900000
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
variable (oldFit:Fintype.card v.prior.V≤v.area.H)
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
local notation "liveRoster" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding))
variable (selected:(v.prior.placement.stage.result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)


variable (B:v.SelectedBoard oldFit (hostRotor (v.prior.vertex.trans (Fin.castLEEmb oldFit)) (DescentGroupPeerOrder.hostRoster v.prior.placement ((v.prior.vertex.trans (Fin.castLEEmb oldFit)).trans Fin.valEmbedding))) selected m parts)
variable (input:Stage.Dated.Operands) (actorPitch countBits base start slots extra gain names:ℕ)
local notation "bytes" => donorNameBits v.stage.k v.stage.Δ
local notation "c₀" => DescentScalarVenueMask.Stage.ingressChart (short:=v.short) («H»:=H) (Z:=J) A v.profile bytes slots v.payload M actorPitch extra gain names
local notation "B₀" => ingressInputs input parts
local notation "token" => DescentScalarVenueMask.Stage.tokens (short:=v.short) A native S v.prior.valid
    (groupRank Fin.valEmbedding ((hosts).trans Fin.valEmbedding)) B.win v.profile lay (Function.Embedding.refl _) hosts slots
local notation "walk" => Gather.reaching liveRoster
local notation "out" now => ((c₀).phase B₀ start w).image now

/-- Through the signed formatter and its earlier peer/mark phases the physical
donor panel and the preceding venue survive in their original lower registers. -/
theorem selected_ingress (old now:Memory w)
    (prior:stageVenue v.prior oldFit input actorPitch countBits base (v.prior.venueRoster oldFit) old)
    (held:∀a<base,now a=old a) (panel:∀p:Row H J M,
      now (parts.base+(row H J M p).val)=m (parts.base+(row H J M p).val))
    (positive:0<actorPitch) (room:(c₀).Room B₀ start w) :
    DescentPackedColony.Reads ((c₀).fieldBank start) (fun h g=>encode (Packed.bits names) (c₀).actorCount
      («fields» walk token (fun h _=>Census.hub A hosts h) v.k gain slots names h g)) (c₀).working (out now) ∧
    Mounted ((c₀).ports start) (DescentSortedRoster.indexed walk) (out now) J (c₀).working ∧
    ∀src:Bank,src.Fits w ((c₀).fullEnd start)→(c₀).core.rows≤ src.size→
      Accessible ((c₀).ports start) src H J (c₀).working w ((c₀).fullEnd start):=by
  apply ingress_from_donor («M»:=M) (short:=v.short) v.prior oldFit input actorPitch countBits base
    B.win B.live v.profile B.births B.issued (A).hub lay bytes slots extra gain names v.payload start parts
    old now prior held _ positive room
  intro p
  refine (panel p).trans ?_
  exact B.source p


local notation "caps" => DescentOrdinaryVenueReturn.shapeSlots D
local notation "gain₀" => DescentHostDegree.gainExponent 20 D
local notation "names₀" => StageVenueTail.OrdinaryRaster.shapes v.area
local notation "bits₀" => max v.fundedUnit extra
local notation "clip" => v.fundedClip extra
local notation "atoms" => DescentScalarVenueMask.Stage.tokens (short:=v.short) A native S v.prior.valid
  (groupRank Fin.valEmbedding ((hosts).trans Fin.valEmbedding)) B.win v.profile lay (Function.Embedding.refl _) hosts caps
local notation "snapshot" now => ((clip).phase B₀ start w).image now

theorem funded_ingress_chart :
    clip = DescentScalarVenueMask.Stage.ingressChart (short:=v.short) («H»:=H) (Z:=J) A v.profile bytes caps
      v.payload M v.area.lanesAt bits₀ gain₀ names₀:=rfl

theorem funded_selected_ingress (old now:Memory w)
    (prior:stageVenue v.prior oldFit input v.area.lanesAt countBits base (v.prior.venueRoster oldFit) old)
    (held:∀a<base,now a=old a) (panel:∀p:Row H J M,
      now (parts.base+(row H J M p).val)=m (parts.base+(row H J M p).val))
    (positive:0<v.area.lanesAt) (room:(clip).Room B₀ start w) (roomEnd:(clip).fullEnd start<2^w) :
    DescentPackedColony.Reads ((clip).fieldBank start) (fun h g=>encode (Packed.bits names₀) (clip).actorCount
      («fields» walk atoms (fun h _=>Census.hub A hosts h) v.k gain₀ caps names₀ h g)) (clip).working (snapshot now) ∧
    Mounted ((clip).ports start) (DescentSortedRoster.indexed walk) (snapshot now) J (clip).working ∧
    Accessible ((clip).ports start) ((clip).fieldBank start) H J (clip).working w ((clip).fullEnd start):=by
  obtain ⟨read,mount,access⟩:=v.selected_ingress oldFit selected m parts B input v.area.lanesAt countBits base start
    caps bits₀ gain₀ names₀ old now prior held panel positive room
  refine ⟨read,mount,access ((clip).fieldBank start) ?_ ?_⟩
  · refine ⟨Nat.two_pow_pos _,?_,Nat.le_refl _⟩
    exact (Nat.le_add_left ..).trans_lt roomEnd
  · exact (clip).core.rowRoom


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
