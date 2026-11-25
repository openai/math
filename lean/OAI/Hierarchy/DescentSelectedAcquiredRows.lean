import OAI.Hierarchy.DescentRegisteredSelectedActors
import OAI.Hierarchy.DescentReachedPaidActorTokens
import OAI.Hierarchy.DescentSelectedBoardMaterial

namespace OAI
/-! # Actual ticket values, logical descriptors and empty words of a single accepted donor board -/
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


variable (B:v.SelectedBoard oldFit liveRoster selected m parts)

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


local notation "nativeRaw" => Stage.nativeParts (short:=v.short) A native S v.prior.valid
  rank B.win (Equiv.refl _) hosts B.live v.profile B.births B.issued liveRoster (A).hub lay
  (donorNameBits v.stage.k v.stage.Δ)
local notation "encodedActors" => Prepare.actors A (Function.Embedding.refl _) hosts
local notation:max "rawToken" x:arg j:arg h:arg g:arg => DepotRAM.ActorInputs.token fmt v.profile slots (2^(v.k+1)*slots)
  (nativeRaw h g) (encodedActors h g) (x,j)

/-- The winning donor's original bytes and occupied masks are the actual
values used for the range gather, also in every row past the original roster. -/
theorem selected_acquired_rows (choiceEq : HEq selected v.choice) :
    Descriptors slots v.k (A).pos (A).block (ticketParent (he:=v.nonnegative) («T»:=v.stage))
      (ticketSlot (c:=v.choice) cut) (owners∘site) v.prior.vertex (Function.Embedding.refl _) moves oldTokens ∧
    (∀x j h g,rawToken x j (h.castLE oldFit) g=oldTokens x j h g) ∧
    (∀x j (h:Fin H) g,Fintype.card v.prior.V≤h.val→ rawToken x j h g=none) ∧
    ∀h,Census.hub A hosts (h.castLE oldFit)=Census.hub A v.prior.vertex h :=by
  refine ⟨v.selected_descriptors oldFit selected m parts B choiceEq,?_⟩
  exact DescentScalarVenueMask.Stage.received_tokens (short:=v.short) A native S v.prior.valid (Equiv.refl _)
    v.prior.vertex oldFit B.win B.live v.profile B.births B.issued (A).hub lay
    (donorNameBits v.stage.k v.stage.Δ) slots

/-- The receipt remains valid on an extensionally equal retained rotor directory.
Restricting its actual code words selects the same original descriptors. -/
theorem selected_material_rows
    (R : Fin H→Fin D→Option (Fin H)) (sameR : R=liveRoster)
    (sheet : v.SelectedBoard oldFit R selected m parts) (chosen : HEq selected v.choice) :
    let acquired := fun x j h g=>DepotRAM.ActorInputs.token fmt v.profile slots (2^(v.k+1)*slots)
      (sheet.material h g) (encodedActors h g) (x,j)
    Descriptors slots v.k (A).pos (A).block (ticketParent (he:=v.nonnegative) («T»:=v.stage))
      (ticketSlot (c:=v.choice) cut) (owners∘site) v.prior.vertex (Function.Embedding.refl _) moves
      (fun x j h g=>acquired x j (h.castLE oldFit) g) ∧
    (∀x j (h : Fin H) g,Fintype.card v.prior.V≤h.val→acquired x j h g=none) ∧
    ∀h,Census.hub A hosts (h.castLE oldFit)=Census.hub A v.prior.vertex h:=by
  subst R
  dsimp only
  obtain ⟨valid,live,ghost,hub⟩:=v.selected_acquired_rows oldFit selected m parts sheet chosen
  exact ⟨(funext fun x=>funext fun j=>funext fun h=>funext fun g=>live x j h g).symm ▸ valid,
    ghost,hub⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
