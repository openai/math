import OAI.Hierarchy.DescentDonatedPublicRead
import OAI.Hierarchy.DescentOrdinaryPublicReindex
import OAI.Hierarchy.DescentDatedSelectedCableKey

namespace OAI
/-! The literal cable and p-block at the registered source index are the original
material cable and fragment read by the returned W row. -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentKernelHistory DescentNetworkPartition
private theorem cable_of_number {P A : Type} {dims p : ℕ} {bits : P → ℕ} (N : Network dims P bits)
    (site : N.Site) (arg : BlockRef p (boundaryWidth N site) ⊕ A) (tag : N.Edge × ℕ)
    (numbers : arg.elim (BlockRef.cableNumber N site) (fun _=>none) = some tag) :
    ∃ (wire : Incident N site) (piece : ℕ) (length : (piece+1)*p ≤ N.width wire.val),
      arg = .inl ⟨.inl wire,piece,length⟩ := by
  rcases arg with ⟨wire|pin,piece,length⟩|hidden
  · exact ⟨wire,piece,length,rfl⟩
  · cases numbers
  · cases numbers
end Hierarchy.DescentBundleHistory
namespace Hierarchy.DescentStageEdgeReceipt.OrdinaryModel
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
open DescentBundleHistory.Normalized
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] BitDescription.scannedRows

variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {H : Type} [Fintype H] [DecidableEq H] {u ε : ℝ}
  (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice)
  (oldID : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (model : OrdinaryModel he T c H)
  (arch : Archive W) (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣T.z)
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "pos" => fun _ : (r).pairs=>T.unitPos
local notation "room" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "sel" => scanWorld he T c
local notation "prior" => sh.selected hp one pin G (r).pick uni pos (r).fit room (r).pack prof whole
local notation "normal" => model.named he T c oldID
local notation "valid" => (show Normalize.CutsEqual T.z normal from ⟨rfl,trivial⟩)
local notation "after" => WorldShape.follow hp T.unitPos unit normal valid prior

set_option maxRecDepth 14000
set_option maxHeartbeats 550000
variable {q : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (same : HEq n (model.named he T c oldID))
local notation "scan" => arch.bit.selected G (r).pick uni pos (r).fit room (r).pack prof
local notation "cur" => afterOrdinary hp one pin ticket arch sh unit
local notation "next" => (ticket.advance arch).bit
local notation "rightNode" x:arg => namedNode ((r).state c) same scan x
local notation "cut" => (ticket.quantum.symm ▸ ticket.cuts)
local notation "nAR" x:arg => named_arity ((r).state c) same scan hp T.unitPos unit prior cut valid x
local notation "rightEdge" x:arg e:arg => namedIncident ((r).state c) same scan x e
local notation "slot" => model.PublicArg he T c oldID arch hp one pin sh unit
local notation "realRead" => model.publicOperand he T c oldID arch hp one pin sh unit
attribute [local irreducible] WorldShape.follow WorldShape.selected WorldShape.transport OrdinaryModel.publicBooks
set_option hygiene false in
local notation "occupiedRead" =>
  named_read (X:=(T.result he).state c) (Y:=scanWorld he T c) (n:=n) (m:=normal)
    (d:=d) (p:=p) (shapes:=R) (grain:=T.z) ((r).state c) same scan hp T.unitPos unit prior cut valid x
    (by
      dsimp only [afterOrdinary,WorldShape.scanned,OrdinaryLink.advance,BitDescription.scanned] at j ⊢
      exact j)
    edge lo fits (by
      dsimp only [afterOrdinary,WorldShape.scanned,OrdinaryLink.advance,BitDescription.scanned] at hit ⊢
      exact hit)

private theorem reindex_occupied_entry (x : NodeOrder.All next) (j : Fin ((((cur).sites x.1).recipe hp).arity x.2))
    (edge : Incident n.result.graph x.1) (lo : ℕ) (fits : (lo+1)*p≤n.result.graph.width edge.val)
    (hit : (((cur).sites x.1).recipe hp).operand x.2 j = .inl ⟨.inl edge,lo,fits⟩) :
    type_of% occupiedRead := occupiedRead
end
end Hierarchy.DescentStageEdgeReceipt.OrdinaryModel
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option maxRecDepth 14000
set_option maxHeartbeats 3500000
set_option quotPrecheck false
set_option cleanup.letToHave false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] atSelected BitDescription.scannedRows DescentLocalArchiveOrder.sourceIndex
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
set_option hygiene false in
local notation "phys" => v.withIssuedSigned
set_option hygiene false in
local notation "S" => v.schedule
set_option hygiene false in
local notation "G" => v.gadget
set_option hygiene false in
local notation "A" => v.prior.placement
set_option hygiene false in
local notation "T" => (A).stage
set_option hygiene false in
local notation "D" => (A).degree
set_option hygiene false in
local notation "r" => 2^v.k
set_option hygiene false in
local notation "J" => (S).groupCount v.age
set_option hygiene false in
local notation "M" => (phys).material.oldLanes
set_option hygiene false in
local notation "H" => v.area.H
set_option hygiene false in
local notation "ss" => (phys).signed
set_option hygiene false in
local notation "native" => v.prior.order.trans Fin.valEmbedding
set_option hygiene false in
local notation "rank" => groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding)
set_option hygiene false in
local notation "grp" => Equiv.refl (Fin J)
set_option hygiene false in
local notation "peers" => rotor A rank
set_option hygiene false in
local notation "home" => scanHomeAt v.nonnegative T
set_option hygiene false in
local notation "color" => scanColorAt v.nonnegative T
set_option hygiene false in
local notation "addr" => nativeAddress v.nonnegative T
set_option hygiene false in
local notation "rr" => BitDescription.scannedRows v.nonnegative T
set_option hygiene false in
local notation "K" => 2^(v.k+1)
set_option hygiene false in
local notation "s" => shape r D (2*(A).cap) v.profile
set_option hygiene false in
local notation "traffic" => nativeTraffic v.world.graph v.world.core home
set_option hygiene false in
local notation "fmt" => v.ticket.depotShape v.short
variable (oldFit:Fintype.card v.prior.V≤H) (R:Fin H→Fin D→Option (Fin H))
set_option hygiene false in
local notation "hosts" => v.prior.vertex.trans (Fin.castLEEmb oldFit)
variable (selected:(v.prior.placement.stage.result v.nonnegative).Choice)
set_option hygiene false in
local notation "lay" => bestLayout (branchWidth G (fun _:(rr).pairs=>(T).z) ((rr).profile selected))
variable {w:ℕ} (m:Memory w) (parts:Bank)

open DescentHaloPackedRebase DescentSharedCableNames
variable (B:v.SelectedBoard oldFit R selected m parts)
variable (choiceEq:HEq selected v.choice) (wide:Fintype.card v.target.V≤ (ss).hosts)
variable (age:v.age<(S).length) (radix:(S).radix=r) (bands:J=(ss).groups*r)
variable (reciprocal:∀v u j,R v j=some u→∃l,R u l=some v)
set_option hygiene false in
local notation "host" => v.target.vertex.trans (Fin.castLEEmb wide)
set_option hygiene false in
local notation "chart" => v.issuedSignedChart
set_option hygiene false in
local notation "pitch" => (phys).materialPitch
set_option hygiene false in
local notation "paths" => (ss).reach
set_option hygiene false in
local notation "space" => v.signedLayout.field_room.1
set_option hygiene false in
local notation "oldStates" => B.material
set_option hygiene false in
local notation "markedBits" => (phys).markBits chart oldFit bands.symm R
open DescentBundleHistory DescentPackedOperand DescentOperandStateBanks Computability.BorderVNP.Crossing
attribute [local irreducible] selectedModelPresentation selectedLocator WorldShape.follow WorldShape.selected WorldShape.transport OrdinaryModel.publicBooks
set_option hygiene false in
local notation "info" => v.selectedModelPresentation oldFit R selected m parts B choiceEq wide age radix reciprocal
set_option hygiene false in
local notation "mod₀" => (info).model
set_option hygiene false in
local notation "world₁" => ((mod₀).named v.nonnegative T selected v.prior.order).result
variable {p kinds : ℕ} (arch : Archive v.world) (hp : 0<p) (one : 1≤kinds) (pin : ∀x,p∣v.bits x)
    (sh : WorldShape p kinds arch.bit) (unit : p∣v.prior.placement.stage.z)
set_option hygiene false in
local notation "sheet" => v.selectedLocator oldFit R selected m parts B choiceEq wide age radix reciprocal arch hp one pin sh unit
set_option hygiene false in
local notation "Use" => OrdinaryModel.PublicUse v.nonnegative T selected v.prior.order mod₀ arch hp one pin sh unit
set_option hygiene false in
local notation "node" => OrdinaryModel.PublicNode v.nonnegative T selected v.prior.order mod₀ arch
set_option hygiene false in
local notation "slotIndex" => OrdinaryModel.PublicArg v.nonnegative T selected v.prior.order mod₀ arch hp one pin sh unit
set_option hygiene false in
local notation "observed" => OrdinaryModel.publicOperand v.nonnegative T selected v.prior.order mod₀ arch hp one pin sh unit


open DescentDatedOperandCoordinates DescentDatedOperandReadPipeline DescentOperandPriorIncidence
set_option hygiene false in
local notation "ℒ" => (phys).resolver
set_option hygiene false in
local notation "E" => (phys).material
set_option hygiene false in
local notation "Γ" => (phys).ticketReadGeometry
set_option hygiene false in
local notation "pos₀" => DescentSharedCableNames.Stage.Positive A
set_option hygiene false in
local notation "cells" => breadth D*DepotRAM.Material.roles fmt
variable (bl : (ℒ).blocks=(E).blocks) (hb : (ℒ).hosts≤(E).hosts) (gs : (ℒ).groups=(E).groups)
variable (orig : Fin (ℒ).jobs→Fin 6→Values Γ (phys).operandShortBits)
    (priorHead : Fin (ℒ).jobs→Fin 4→Values Γ ((ℒ).size+2)) (born : Fin (ℒ).jobs→Fin 3→Values Γ (phys).bornBook.bits)
set_option hygiene false in
local notation "serial" => v.retainedSerial oldFit R selected m parts B choiceEq wide age radix bands reciprocal
set_option hygiene false in
local notation "peer" => v.retainedPeer oldFit R selected m parts B choiceEq wide age radix bands reciprocal
set_option hygiene false in
local notation "data" => (phys).originalValues ((phys).sampleHeads bl hb gs orig priorHead born
   ((phys).wideMaterialValues R B.material bands serial peer) ((phys).narrowValue R))
variable (j : Fin (ℒ).jobs) (h : Fin (ℒ).hosts) (y : Fin (ℒ).groups)
set_option hygiene false in
local notation "x₀" => (phys).receiverBlock bl j
set_option hygiene false in
local notation "h₀" => h.castLE hb
set_option hygiene false in
local notation "y₀" => y.cast gs

set_option hygiene false in
local notation "rawType" => DescentRawCablePanel.Live A (rr).pick
set_option hygiene false in
local notation "anchor₀" raw:arg => (⟨DescentCableDonorNames.anchor (rr).pick (raw).val,(raw).property⟩ : pos₀)
set_option hygiene false in
local notation "src₀" raw:arg => v.world.graph.src (anchor₀ raw).val
set_option hygiene false in
local notation "seat" raw:arg => ((A).block (src₀ raw),DescentSharedCableNames.Stage.outgoing A native S v.prior.valid
    (anchor₀ raw),DescentCableDonorNames.role (raw).val)
set_option hygiene false in
local notation "row" path:arg raw:arg => finProdFinEquiv (path,Ticket.seatNo (seat raw))
set_option hygiene false in
local notation "cutCore" raw:arg => DescentOrdinarySignedMeta.markRole (DescentCableDonorNames.role (raw).val)
  (decide ((anchor₀ raw).val∈v.world.core))

open DescentLocalArchiveOrder DescentBundleHistory.Normalized
set_option hygiene false in
local notation "ac" => v.atSelected selected choiceEq
set_option hygiene false in
local notation "ticket" => (ac).link
set_option hygiene false in
local notation "scan" => arch.bit.selected G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit
  (fun _=>le_refl (T).z) (rr).pack ((rr).profile selected)
set_option hygiene false in
local notation "selectedShape" => sh.selected hp one pin G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit
  (fun _=>le_refl (T).z) (rr).pack ((rr).profile selected) (fun _=>unit)
set_option hygiene false in
local notation "input" => (rr).state selected
set_option hygiene false in
local notation "aligned" => (ac).originalNorm.trans (info).normalized
set_option hygiene false in
local notation "result" => (mod₀).named v.nonnegative T selected v.prior.order
set_option hygiene false in
local notation "valid" => (show Normalize.CutsEqual (T).z result from ⟨rfl,trivial⟩)
set_option hygiene false in
local notation "cuts" => ((ticket).quantum.symm ▸ (ticket).cuts)
set_option hygiene false in
local notation "next" => ((ticket).advance arch).bit
set_option hygiene false in
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
set_option hygiene false in
local notation "net" => rawGraph v.nonnegative T selected
set_option hygiene false in
local notation "names" => NodeOrder.physicalNames arch.bit G (rr).pick (fun _=>(T).z) (fun _=>le_refl (T).z) ((rr).profile selected)
set_option hygiene false in
local notation "atNode" x:arg => (names).symm (roots ticket arch x)
set_option hygiene false in
local notation "base₀" => physicalShape v.world arch.bit G (rr).pick (fun _=>(T).z) (fun _=>le_refl (T).z) ((rr).profile selected)
  hp sh.sites sh.edges pin (fun _=>unit)
set_option hygiene false in
local notation "argAt" x:arg j:arg => ((base₀ (atNode x).1).recipe hp).operand (atNode x).2 (sourceIndex ticket arch hp one pin sh unit x j)

section
variable (model : OrdinaryModel v.nonnegative T selected (Fin J × v.prior.V))
    (normalized : HEq v.normalize (model.named v.nonnegative T selected v.prior.order))
set_option hygiene false in
local notation "sourceUse" => OrdinaryModel.PublicUse v.nonnegative T selected v.prior.order model arch hp one pin sh unit
set_option hygiene false in
local notation "sourceNode" => OrdinaryModel.PublicNode v.nonnegative T selected v.prior.order model arch
set_option hygiene false in
local notation "sourceResult" => model.named v.nonnegative T selected v.prior.order
set_option hygiene false in
local notation "sourceValid" => (show Normalize.CutsEqual (T).z sourceResult from ⟨rfl,trivial⟩)
set_option hygiene false in
local notation "sourceAlignment" => (ac).originalNorm.trans normalized
attribute [local irreducible] NodeOrder.selectedNames NodeOrder.followNames NodeOrder.castNames
include unit in
private theorem source_number (x : NodeOrder.All next) (arg : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (use : sourceUse) (where_ : use.node=namedNode input sourceAlignment scan x)
    (what : HEq use.arg (arg.cast (named_arity input sourceAlignment scan hp (T).unitPos unit selectedShape cuts sourceValid x))) :
    (argAt x arg).elim (fun w=>w.cableNumber net (atNode x).1) (fun _=>none)=some (use.cable.val,use.chunk) :=by
  have root : names (atNode x)=NodeOrder.selectedNames arch.bit G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit
      (fun _=>le_refl (T).z) (rr).pack ((rr).profile selected) (NodeOrder.followNames sourceResult scan use.node) :=by
    let selectNames := NodeOrder.selectedNames arch.bit G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos)
      (rr).fit (fun _=>le_refl (T).z) (rr).pack ((rr).profile selected)
    let walkNames := NodeOrder.followNames sourceResult scan
    have vertexEq := congrArg (fun vtx : sourceNode => selectNames (walkNames vtx)) where_
    have fromNorm := congrArg (fun a=>selectNames a) (named_root input sourceAlignment scan x)
    exact ((names).apply_symm_apply _).trans (fromNorm.symm.trans vertexEq.symm)
  have index:arg.val=use.arg.val:=by
    have extent:=congrArg (fun a : sourceNode=>(((WorldShape.follow hp (T).unitPos unit sourceResult sourceValid selectedShape).sites a.1).recipe hp).arity a.2) where_
    exact (fin_number extent what).symm
  exact use.raw_number v.nonnegative T selected v.prior.order model arch hp one pin sh unit
    (atNode x) (sourceIndex ticket arch hp one pin sh unit x arg) root
    ((sourceIndex_val ticket arch hp one pin sh unit x arg).trans index)

variable (modelWorld : v.normalize.result = (model.named v.nonnegative T selected v.prior.order).result)
include unit in
private theorem original_cable_and_chunk (x : NodeOrder.All next) (arg : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (u : sourceUse) (home_ : u.node=namedNode input sourceAlignment scan x)
    (slot_ : HEq u.arg (arg.cast (named_arity input sourceAlignment scan hp (T).unitPos unit selectedShape cuts sourceValid x)))
    (wire : Incident net (atNode x).1) (piece : ℕ) (length : (piece+1)*p≤(net).width wire.val)
    (seen : argAt x arg=.inl ⟨.inl wire,piece,length⟩) :
    (u.cable.val,u.chunk)=(wire.val,piece) := by
  have nums := source_number (v:=v) (selected:=selected) (model:=model) (normalized:=normalized)
    (choiceEq:=choiceEq) (arch:=arch) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) x arg u home_ slot_
  let number := fun a : type_of% (argAt x arg) =>
    Sum.elim (DescentBundleHistory.BlockRef.cableNumber net (atNode x).1) (fun _=>none) a
  exact Option.some.inj (nums.symm.trans (congrArg number seen))
include unit in
private theorem pointer_at_registered_source (x : NodeOrder.All next) (arg : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (u : sourceUse) (home_ : u.node=namedNode input sourceAlignment scan x)
    (slot_ : HEq u.arg (arg.cast (named_arity input sourceAlignment scan hp (T).unitPos unit selectedShape cuts sourceValid x)))
    (wire : Incident net (atNode x).1) (piece : ℕ) (length : (piece+1)*p≤(net).width wire.val)
    (seen : argAt x arg=.inl ⟨.inl wire,piece,length⟩)
    (edge : Incident (ac).norm.result.graph x.1) (lo : ℕ) (fit : (lo+1)*p≤(ac).norm.result.graph.width edge.val)
    (value : Pointer)
    (returned : (u.cable.val,u.chunk)=(wire.val,piece) →
      value = v.target.firstCable hp (Reached.originalSite modelWorld (namedNode input sourceAlignment scan x).1)
        (Reached.originalIncident modelWorld (namedNode input sourceAlignment scan x).1 (namedIncident input sourceAlignment scan x edge))
        lo (Reached.original_fit modelWorld (namedNode input sourceAlignment scan x).1 (namedIncident input sourceAlignment scan x edge)
          lo (fit.trans_eq (named_width input sourceAlignment scan x edge)))) :
    value=(ac).next.firstCable hp x.1 edge lo fit := by
  have pair := original_cable_and_chunk (v:=v) (selected:=selected) (model:=model) (normalized:=normalized) (choiceEq:=choiceEq)
     (arch:=arch) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit) x arg u home_ slot_ wire piece length seen
  exact (returned pair).trans (reached_pointer input sourceAlignment scan hp (ac).next v.target (ac).originalNext modelWorld x edge lo fit)

end

theorem dated_source_exists
    {F P : Type} [Field F] (v:PhysicalOrdinary F P)
    (oldFit:Fintype.card v.prior.V≤H) (R:Fin H→Fin D→Option (Fin H))
    (selected:(v.prior.placement.stage.result v.nonnegative).Choice)
    {w:ℕ} (m:Memory w) (parts:Bank)
    (B:v.SelectedBoard oldFit R selected m parts)
    (choiceEq:HEq selected v.choice) (wide:Fintype.card v.target.V≤ (ss).hosts)
    (age:v.age<(S).length) (radix:(S).radix=r)
    (reciprocal:∀v u j,R v j=some u→∃l,R u l=some v)
    {p kinds : ℕ} (arch : Archive v.world) (hp : 0<p) (one : 1≤kinds) (pin : ∀x,p∣v.bits x)
    (sh : WorldShape p kinds arch.bit) (unit : p∣v.prior.placement.stage.z)
    (x : NodeOrder.All next) (arg : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (edge : Incident (ac).norm.result.graph x.1) (lo : ℕ) (fit : (lo+1)*p≤(ac).norm.result.graph.width edge.val)
    (hit : (((after).sites x.1).recipe hp).operand x.2 arg=.inl ⟨.inl edge,lo,fit⟩) :
    ∃(wire : Incident net (atNode x).1) (piece : ℕ) (length : (piece+1)*p≤(net).width wire.val),
      argAt x arg=.inl ⟨.inl wire,piece,length⟩ :=by
  have current := OrdinaryModel.reindex_occupied_entry v.nonnegative T selected v.prior.order (mod₀) arch hp one pin sh unit
    (ticket) aligned x arg edge lo fit hit
  have origin := (mod₀).public_origin v.nonnegative T selected v.prior.order arch hp one pin sh unit
    (namedNode input aligned scan x) _ (namedIncident input aligned scan x edge) lo _ current
  let use := origin.choose
  have position := origin.choose_spec.1
  have index := origin.choose_spec.2
  have literal := source_number (v:=v) (selected:=selected) (choiceEq:=choiceEq) (model:=mod₀)
    (normalized:=(info).normalized) (arch:=arch) (hp:=hp) (one:=one) (pin:=pin) (sh:=sh) (unit:=unit)
    x arg use position index
  exact DescentBundleHistory.cable_of_number net (atNode x).1 (argAt x arg) (use.cable.val,use.chunk) literal

/-- Both reads use the same selected normalization and return the same physical
socket, its original chunk and its chronological reached pointer. -/
theorem dated_source_pointer
    {F P : Type} [Field F] (v:PhysicalOrdinary F P)
    (oldFit:Fintype.card v.prior.V≤H) (R:Fin H→Fin D→Option (Fin H))
    (selected:(v.prior.placement.stage.result v.nonnegative).Choice)
    {w:ℕ} (m:Memory w) (parts:Bank)
    (B:v.SelectedBoard oldFit R selected m parts)
    (choiceEq:HEq selected v.choice) (wide:Fintype.card v.target.V≤ (ss).hosts)
    (age:v.age<(S).length) (radix:(S).radix=r) (bands:J=(ss).groups*r)
    (reciprocal:∀v u j,R v j=some u→∃l,R u l=some v)
    {p kinds : ℕ} (arch : Archive v.world) (hp : 0<p) (one : 1≤kinds) (pin : ∀x,p∣v.bits x)
    (sh : WorldShape p kinds arch.bit) (unit : p∣v.prior.placement.stage.z)
    (bl : (ℒ).blocks=(E).blocks) (hb : (ℒ).hosts≤(E).hosts) (gs : (ℒ).groups=(E).groups)
    (orig : Fin (ℒ).jobs→Fin 6→Values Γ (phys).operandShortBits)
    (priorHead : Fin (ℒ).jobs→Fin 4→Values Γ ((ℒ).size+2)) (born : Fin (ℒ).jobs→Fin 3→Values Γ (phys).bornBook.bits)
    (j : Fin (ℒ).jobs) (h : Fin (ℒ).hosts) (y : Fin (ℒ).groups)
    (x : NodeOrder.All next) (arg : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (edge : Incident (ac).norm.result.graph x.1) (lo : ℕ) (fit : (lo+1)*p≤(ac).norm.result.graph.width edge.val)
    (hit : (((after).sites x.1).recipe hp).operand x.2 arg=.inl ⟨.inl edge,lo,fit⟩)
    (raw : rawType) (wire : Incident net (atNode x).1) (piece : ℕ) (length : (piece+1)*p≤(net).width wire.val)
    (seen : argAt x arg=.inl ⟨.inl wire,piece,length⟩) (isRaw : raw.val=wire.val)
    (wireFit : v.target.placement.cap≤2^(ss).fieldBits) (peerFit : v.target.placement.degree≤2^(ss).fieldBits)
    (wireWide : v.target.placement.cap≤2^((ℒ).size+2)) (peerWide : v.target.placement.degree≤2^((ℒ).size+2))
    (recv : Fin H) (atHost : DepotRAM.Material.Route.receiver H pitch h₀=some recv)
    (vHost : ((ac).next.vertex ((ac).next.placement.pos x.1).2).val=(h₀).val)
    (vBand : ((ac).next.placement.pos x.1).1.val=(y₀).val) (vBlock : ((ac).next.placement.block x.1).val=(x₀).val)
    (path : Fin (breadth D)) (route : Gather.select (Gather.reaching R) recv path=some (hosts ((A).pos (src₀ raw)).2))
    (bitsIn cut : Cell ((ℒ).size+2)) (bitsRead : bitsIn.val=piece) (cutRead : cut.val=(T).z/p) :
    Pointer.ofKey 0 (resolve (Public.fragment (cutCore raw)
      (((data).raw j 7 (row path raw) h y).val:Cell ((ℒ).size+2))
      (((data).raw j 6 (row path raw) h y).val:Cell ((ℒ).size+2)) bitsIn cut))=
      (ac).next.firstCable hp x.1 edge lo fit :=by
  have read := OrdinaryModel.reindex_occupied_entry v.nonnegative T selected v.prior.order (mod₀) arch hp one pin sh unit
    (ticket) aligned x arg edge lo fit hit
  have xyz := reached_coords input aligned scan (ac).next v.target (ac).originalNext (info).same x
  have reply := v.returned_public_pointer oldFit R selected m parts B choiceEq wide age radix bands
    reciprocal arch hp one pin sh unit bl hb gs orig priorHead born j h y (namedNode input aligned scan x)
    _ (namedIncident input aligned scan x edge) lo _ read wireFit peerFit wireWide peerWide recv atHost
    ((congrArg Prod.fst xyz).trans vHost) ((congrArg (fun t=>t.2.1) xyz).trans vBand)
    ((congrArg (fun t=>t.2.2) xyz).trans vBlock)
  let use := reply.choose
  have where_ := reply.choose_spec.1
  have what := reply.choose_spec.2.1
  have out := reply.choose_spec.2.2
  exact pointer_at_registered_source (v:=v) (selected:=selected) (choiceEq:=choiceEq) (model:=mod₀)
    (normalized:=(info).normalized) (modelWorld:=(info).same) (arch:=arch) (hp:=hp) (one:=one)
    (pin:=pin) (sh:=sh) (unit:=unit) x arg use where_ what wire piece length seen edge lo fit _
    (fun pair => out raw (isRaw.trans (congrArg Prod.fst pair).symm) path route bitsIn cut
      (bitsRead.trans (congrArg Prod.snd pair).symm) cutRead)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

-- Keep premise-search indexing local to signatures within the measured export budget.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun current =>
    ["dated_source_exists", "dated_source_pointer"] ++ current

end OAI
