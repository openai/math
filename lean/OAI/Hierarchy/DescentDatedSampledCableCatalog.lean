import OAI.Hierarchy.DescentDatedCableJobCatalog
import OAI.Hierarchy.DescentDatedPostedParentNumbers
import OAI.Hierarchy.DescentSelectedBoardMaterial
import OAI.Hierarchy.DescentDatedNativeOccurrenceTicket

namespace OAI
/-! # Actual elected source and sibling cells in the ordinary operand reader -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket
theorem anchor_small {B C b : ℕ} (born : Bool) (z : SocketSeat B C) (space : B*C*11 < 2^b) (f : Fin 5) :
    anchor born z f < 2^b :=by
  let role:=if born then 0 else z.2.2.val
  have roleBound : role ≤ z.2.2.val :=by dsimp [role];split <;> omega
  have raw : 11*(z.1.val*C+z.2.1.val)+z.2.2.val < B*C*11 :=by
    have fin:=(seatNo z).isLt
    simp only [seatNo,finProdFinEquiv_apply_val] at fin
    convert fin using 1 <;> ring
  have positive : 0<C:=lt_of_le_of_lt (Nat.zero_le _) z.2.1.isLt
  have lower:=Nat.le_mul_of_pos_right z.1.val positive
  rw [anchor_at]
  change ![1+z.1.val,1+z.2.1.val,role,1+11*z.2.1.val+role,1+11*(z.1.val*C+z.2.1.val)+role] f < _
  fin_cases f <;> dsimp <;> omega
end Hierarchy.DescentDatedOperandCoordinates.Ticket

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000
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
variable (oldFit : Fintype.card v.prior.V ≤ v.area.H)
    (R : Fin v.area.H → Fin v.prior.placement.degree → Option (Fin v.area.H))
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected : (v.prior.placement.stage.result v.nonnegative).Choice)
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

variable (B:v.SelectedBoard oldFit R selected m parts)

open DescentDatedOperandCoordinates DescentDatedOperandReadPipeline DescentOperandPriorIncidence
open DescentHaloPackedRebase DescentSharedCableNames
local notation "ℒ" => (phys).resolver
local notation "E" => (phys).material
local notation "Γ" => (phys).ticketReadGeometry
local notation "pos_" => DescentSharedCableNames.Stage.Positive A
local notation "from_" q:arg => v.world.graph.src (q).val
local notation "block_" q:arg => (A).block (from_ q)
local notation "old_" => DescentSharedCableNames.Stage.outgoing A native S v.prior.valid
local notation "scene" => B.material
variable (bl : v.withIssuedSigned.resolver.blocks=v.withIssuedSigned.material.blocks) (hb : v.withIssuedSigned.resolver.hosts≤v.withIssuedSigned.material.hosts) (gs : v.withIssuedSigned.resolver.groups=v.withIssuedSigned.material.groups)
    (bands : (v.schedule.groupCount v.age)=v.withIssuedSigned.material.groups*v.withIssuedSigned.material.blocks)
local notation "seats" => breadth D*DepotRAM.Material.roles fmt
local notation "col" => (Fin (E).hosts→Fin (E).groups→Cell (E).fieldBits)
variable (serial peer : Fin v.withIssuedSigned.material.blocks→Fin (breadth v.prior.placement.degree*DepotRAM.Material.roles (v.ticket.depotShape v.short))→(Fin v.withIssuedSigned.material.hosts → Fin v.withIssuedSigned.material.groups → Cell v.withIssuedSigned.material.fieldBits))
variable (orig : Fin v.withIssuedSigned.resolver.jobs→Fin 6→Values v.withIssuedSigned.ticketReadGeometry v.withIssuedSigned.operandShortBits)
    (prior : Fin v.withIssuedSigned.resolver.jobs→Fin 4→Values v.withIssuedSigned.ticketReadGeometry (v.withIssuedSigned.resolver.size+2)) (born : Fin v.withIssuedSigned.resolver.jobs→Fin 3→Values v.withIssuedSigned.ticketReadGeometry v.withIssuedSigned.bornBook.bits)
local notation "data" => (phys).originalValues ((phys).sampleHeads bl hb gs orig prior born
  ((phys).wideMaterialValues R scene bands serial peer) ((phys).narrowValue R))
variable (j : Fin v.withIssuedSigned.resolver.jobs) (h : Fin v.withIssuedSigned.resolver.hosts) (y : Fin v.withIssuedSigned.resolver.groups) (recv : Fin v.area.H)
local notation "grpAt" => (finProdFinEquiv (y.cast gs,(phys).receiverBlock bl j)).cast bands.symm
variable (atHost : DepotRAM.Material.Route.receiver v.area.H v.withIssuedSigned.materialPitch (h.castLE hb)=some recv)
local notation "modeKey" p:arg x:arg old:arg mode:arg => finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,mode)))

theorem real_catalogue_room : r*(A).cap*11 < 2^(E).fieldBits :=by
  let q:=v.signedLayout
  have bits:=v.signedLayout.field_room.1
  have sub_:q.residentSlots≤q.tickets:=Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)
  change q.residentSlots<2^q.fieldBits
  change q.rawAlphabet≤2^q.fieldBits at bits
  unfold SignedStage.rawAlphabet at bits
  dsimp only at bits
  omega

private theorem matcherAt (cfg : DepotRAM.Shape) (paths : ℕ) (p : Fin paths) (x : Fin cfg.blocks)
    (old : Fin cfg.cap) (mode : Fin 3) (f₀ : Fin 5) :
    DescentDatedOperandPages.matcherIndex cfg paths
      (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,mode)))) f₀ =
      (p, if h : mode.val < 2 then DescentDatedOperandPages.anchor cfg x old ⟨mode.val,h⟩ f₀
        else DescentDatedOperandPages.sibling cfg x old f₀) := by
  simp only [DescentDatedOperandPages.matcherIndex, Equiv.symm_apply_apply]

include atHost in
theorem returned_anchor_pages (p : Fin (breadth D)) (q q' : pos_) (mode : Fin 3) (role : Fin 11)
    (C : Stage.CablePort A v.nonnegative q mode q' role)
    (visits : Gather.select (Gather.reaching R) recv p=some (hosts ((A).pos (from_ q)).2))
    (sourceCohort : grpAt=((A).pos (from_ q)).1) (f : Fin 5) :
    ((data).anchor j f (modeKey p (block_ q) (old_ q) mode) h y).val =
      Ticket.anchor false (block_ q',old_ q',role) f :=by
  let idx:=modeKey p (block_ q) (old_ q) mode
  let place:=(A).pos (from_ q)
  let donor:=hosts place.2
  let ptr:=if live : mode.val<2 then DescentDatedOperandPages.anchor fmt (block_ q) (old_ q) ⟨mode.val,live⟩ f
           else DescentDatedOperandPages.sibling fmt (block_ q) (old_ q) f
  have loc : (phys).matchAnchorIndex idx f=(p,ptr) :=by
    exact matcherAt fmt (breadth D) p (block_ q) (old_ q) mode f
  have path : Gather.select (Gather.reaching R) recv ((phys).matchAnchorIndex idx f).1=some donor :=by
    rw [loc];exact visits
  have load:=(phys).sampled_anchor_number bl hb gs R scene bands serial peer orig prior born j h y recv donor atHost idx f path
  erw [loc,sourceCohort] at load
  have issued:=Stage.CablePort.page_at A native S v.prior.valid grp hosts B.win v.nonnegative B.live v.profile
    B.births B.issued (A).hub lay (donorNameBits v.stage.k v.stage.Δ) v.prior.valid.coordinates B.named B.small
    B.winning B.degree B.ordered B.topo B.matched B.width B.topology (E).fieldBits C (scene donor place.1) rfl f
  have final_:=(congrArg Fin.val issued)
  exact load.trans (final_.trans (Fin.val_cast_of_lt
    (Ticket.anchor_small false (block_ q',old_ q',role) (real_catalogue_room v) f)))

local notation "live_" => DescentRawCablePanel.Live A (rr).pick
local notation "qAt" raw:arg => (⟨DescentCableDonorNames.anchor (rr).pick (raw).val,(raw).property⟩ : pos_)
local notation "whereAt" raw:arg => hosts ((A).pos (from_ (qAt raw))).2
local notation "seedAt" raw:arg => ((A).pos (from_ (qAt raw))).1
local notation "seatAt" raw:arg => ((block_ (qAt raw),old_ (qAt raw),DescentCableDonorNames.role (raw).val):DepotRAM.Material.Seat fmt)

/-- The flattened incoming source key recovers all four original coordinates:
old cohort, old block, outgoing port and the raw eleven-way role. -/
theorem raw_catalogue_address (raw : live_) :
    let index := DescentRawCablePanel.slot A S v.prior.valid native hosts grp (rr).pick raw
    index.1=whereAt raw ∧ OrdinaryLink.groupSeat index.2=(seedAt raw,seatAt raw) :=by
  constructor
  · rfl
  · simp only [DescentRawCablePanel.slot,Function.Embedding.coeFn_mk,OrdinaryLink.groupSeat,
      Equiv.symm_apply_apply,Equiv.refl_apply]
    rfl

include atHost in
/-- The literal six packed inputs of a chosen cable job on the actual selected
board. Corrected W path numbers do not modify these measured material pages. -/
theorem returned_raw_pages (p : Fin (breadth D)) (raw : live_)
    (visits : Gather.select (Gather.reaching R) recv p=some (whereAt raw))
    (sourceCohort : grpAt=seedAt raw) (f : Fin 6) :
    ((data).raw j (f.castLE (by decide : 6≤8)) (finProdFinEquiv (p,DepotRAM.Material.seatIndex fmt (seatAt raw))) h y).val =
      (DepotRAM.Material.rawObserved fmt (phys).materialFormat (B.material (whereAt raw) (seedAt raw))
        (digest (DepotRAM.Material.reverseEntries fmt R (whereAt raw))) (seatAt raw) f).val :=by
  have actual:=(phys).sampled_material_numbers bl hb gs R scene bands serial peer orig prior born j h y recv
    (whereAt raw) atHost p (seatAt raw) visits f
  exact actual.trans (congrArg (fun group =>
    (DepotRAM.Material.rawObserved fmt (phys).materialFormat (B.material (whereAt raw) group)
      (digest (DepotRAM.Material.reverseEntries fmt R (whereAt raw))) (seatAt raw) f).val) sourceCohort)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
