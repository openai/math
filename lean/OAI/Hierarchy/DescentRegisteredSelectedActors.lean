import OAI.Hierarchy.DescentRegisteredSelectedIngress
import OAI.Hierarchy.DescentReachedOwnerEvidence
import OAI.Hierarchy.DescentMaterialActorPadding

namespace OAI
/-! # The accepted donor board counts every paid actor at its measured normalized address -/
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
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
attribute [local irreducible] Stage.nativeParts topologyWords Gather.flat terrain spread pairNumber slabPacking Stage.slot
  DescentScalarVenueMask.Stage.tokens BitDescription.scannedRows
section DatedWinner
variable {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {S : DescentCompiler.AtomSchedule} {q rate eps : ℝ} {k i z deg nz nd wire hist : ℕ}
    {prior : Reached W G q eps S k i z deg wire hist} {he : 0 ≤ eps} {T : StageInput W G rate eps}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {target : Reached n.result G q eps S k (i+1) nz nd wire hist}
    (link : OrdinaryLink prior he T c n target) (short profile : ℕ)
    (sel : (prior.placement.stage.result he).Choice)
open DescentLocalArchiveOrder DescentScalarVenueMask DescentGroupPeerOrder
local notation "oldA" => prior.placement
local notation "addressOld" => nativeAddress he prior.placement.stage
local notation "homeOld" => scanHomeAt he prior.placement.stage
local notation "colorOld" => scanColorAt he prior.placement.stage
local notation "realRank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
local notation "oldOrder" => prior.order.trans Fin.valEmbedding
local notation "oldScan" => BitDescription.scannedRows he prior.placement.stage
local notation "newScan" => BitDescription.scannedRows he T
local notation "oldLay" => bestLayout (branchWidth G (fun _ : (oldScan).pairs => prior.placement.stage.z) ((oldScan).profile sel))
local notation "newLay" => bestLayout (branchWidth G (fun _ : (newScan).pairs => T.z) ((newScan).profile c))
local notation "shelfSlots" => DescentOrdinaryVenueReturn.shapeSlots prior.placement.degree

private theorem dated_descriptors_of_winner {numBits : ℕ}
    (win : Fin (S.groupCount i) × prior.V → Fin (2^k) → Cell numBits)
    (named : prior.placement.SiteNamed realRank)
    (ordered : ∀e f,oldOrder e<oldOrder f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (small : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val<2^short)
    (hit : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val=1+2*heap (addressOld (homeOld u)).2+(colorOld u).toNat)
    (bound : prior.placement.degree<2^short) (chosen : HEq sel c) :
    Descriptors shelfSlots k prior.placement.pos prior.placement.block (ticketParent (he:=he) (T:=T))
      (ticketSlot (c:=c) link) (((activeChart link).key he T c) ∘ (GadgetNetwork.newSite W.graph (newScan).pick newLay (newScan).pack))
      prior.vertex (Function.Embedding.refl _) (rotor oldA realRank)
      (DescentScalarVenueMask.Stage.tokens (short:=short) oldA oldOrder S prior.valid realRank win profile oldLay
        (Function.Embedding.refl _) prior.vertex shelfSlots) := by
  obtain rfl := link.sourceRate
  obtain rfl := eq_of_heq link.placement
  obtain rfl := eq_of_heq chosen
  exact original_routes (short:=short) link win profile named ordered small hit bound
end DatedWinner

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
variable (oldFit : Fintype.card v.prior.V ≤ v.area.H)
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
local notation "liveRoster" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A ((hosts).trans Fin.valEmbedding))
variable (selected : (v.prior.placement.stage.result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)


variable (B : v.SelectedBoard oldFit (hostRotor (v.prior.vertex.trans (Fin.castLEEmb oldFit)) (DescentGroupPeerOrder.hostRoster v.prior.placement ((v.prior.vertex.trans (Fin.castLEEmb oldFit)).trans Fin.valEmbedding))) selected m parts)

open DescentLocalArchiveOrder DescentScalarVenueMask
local notation "slots" => DescentOrdinaryVenueReturn.shapeSlots D
local notation "oldTokens" => DescentScalarVenueMask.Stage.tokens (short:=v.short) A native S v.prior.valid
  rank B.win v.profile lay (Function.Embedding.refl _) v.prior.vertex slots
local notation "fullTokens" => DescentScalarVenueMask.Stage.tokens (short:=v.short) A native S v.prior.valid
  (groupRank Fin.valEmbedding ((hosts).trans Fin.valEmbedding)) B.win v.profile lay (Function.Embedding.refl _) hosts slots
local notation "cut" => v.ticket
local notation "rows" => BitDescription.scannedRows v.nonnegative v.stage
local notation "feeLayout" => bestLayout (branchWidth G (fun _ : (rows).pairs=>v.stage.z) ((rows).profile v.choice))
local notation "site" => GadgetNetwork.newSite v.world.graph (rows).pick feeLayout (rows).pack
local notation "owners" => (activeChart cut).key v.nonnegative v.stage v.choice
local notation "moves" => rotor A rank

theorem selected_descriptors (choiceEq:HEq selected v.choice):
    Descriptors slots v.k (A).pos (A).block (ticketParent (he:=v.nonnegative) («T» := v.stage))
      (ticketSlot (c:=v.choice) cut) (owners∘site) v.prior.vertex (Function.Embedding.refl _) moves oldTokens:=by
  exact dated_descriptors_of_winner v.ticket v.short v.profile selected B.win B.named B.ordered B.small B.winning B.degree choiceEq

theorem selected_token_rows :
    (∀x j h g,fullTokens x j (Fin.castLEEmb oldFit h) g=oldTokens x j h g) ∧
    (∀x j (h:Fin H) g,Fintype.card v.prior.V≤h.val→fullTokens x j h g=none) ∧
    ∀h,Census.hub A hosts (Fin.castLEEmb oldFit h)=Census.hub A v.prior.vertex h:=by
  have same:(hosts).trans Fin.valEmbedding=v.prior.vertex.trans Fin.valEmbedding:=by ext x;rfl
  simp only [same]
  refine ⟨?_,?_,fun h=>DescentScalarVenueMask.Stage.hub_padded v.prior.vertex (Fin.castLEEmb oldFit) A h⟩
  · intro x j h g
    exact DescentScalarVenueMask.Stage.tokens_padded (short:=v.short) (Function.Embedding.refl _) v.prior.vertex
      (Fin.castLEEmb oldFit) A native S v.prior.valid rank B.win v.profile lay slots x j h g
  · intro x j h g outside
    apply DescentScalarVenueMask.Stage.tokens_absent (short:=v.short) (Function.Embedding.refl _) v.prior.vertex
      (Fin.castLEEmb oldFit) A native S v.prior.valid rank B.win v.profile lay slots x j h g
    intro t equal
    have value:=congrArg Fin.val equal
    change t.val=h.val at value
    have small:=t.isLt
    omega
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
