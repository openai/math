import OAI.Hierarchy.DescentNamedRangeAtPublicActor
import OAI.Hierarchy.DescentVacantRangeControls
import OAI.Hierarchy.DescentResetRecordedPrimary

namespace OAI
/-! # Posted range words at empty physical reset coordinates -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
private theorem compact_unkept {used : ℕ} (placement : DescentResetRetainedPlacement.Chart)
    (batch : DescentResetRetainedPlacement.Batch) (keep : Fin placement.shapes → Bool)
    (names : Fin used → Fin placement.sparse)
    (values : Fin (batch.fields * placement.shapes) → Fin placement.oldHosts →
      Fin (placement.groups * placement.blocks) → Cell batch.bits)
    (index : Fin batch.fields) (column : Fin placement.blocks)
    (host : Fin placement.newHosts) (group : Fin placement.groups)
    (unused : ∀ h : host.val < used, ¬keep (placement.shape (names ⟨host.val,h⟩)) = true) :
    DescentRetainedTargetPlacement.Chart.compact placement batch keep names values index column host group = 0 := by
  unfold DescentRetainedTargetPlacement.Chart.compact DescentResetDenseOperand.dense
  split
  next h => exact ite_eq_right (unused h)
  next => rfl

variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "datedInput" pr:arg sc:arg => I₀ previousMeta previousArguments initial pr sc
set_option hygiene false
local notation "u" => datedInput prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "HH" => S.hostSize age
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph ((Z).k-(T).commonDepth) (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor
local notation "actorBase" => (v).middle.stop base₀
local notation "setup" => (v).setup
local notation "r" => (setup).retained
local notation "ctrl" => (v).controlRegisters
local notation "controlStart" => (v).controlFloor base₀
local notation "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
open DescentSixParty.Chronology.DatePorts
open DescentSixParty.ClosedReset.Window DescentRetainedRangeDigits
local notation "amountRows" => DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom dd cd ready archived μ measured actors
local notation "directory" hr:arg sr:arg => fun j : Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hr sr)
local notation "priorRows" => DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom dd ready inputMem cd μ measured actors
local notation "actorAt" => actualBit B B.next.valid.host rh rg block
local notation "kept" => ∃(inside:rh.val<Fintype.card B.next.V) (hr:HH=(setup).placement.oldHosts)
  (sr:rows=(setup).placement.shapes), (u).menu.keep ((setup).placement.shape ((directory hr sr) ⟨rh.val,inside⟩))=true

set_option hygiene true
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
/-- On a masked actor, a nonzero posted range word can come only from a retained
row of the original table at a real host.  This includes padded date coordinates. -/
theorem DateInputs.range_panel_inactive
    (prepared : (rc).PreparedFits book) (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (dd:venue.degree=D) (cd:input.placement.cap=cap) (ready:(u).Ready)
    (archived:(r).Values) (μ:DescentGL.Layout (E).dim) (measured actors:Memory w)
    (inputMem : Memory w)
    (requests : amountRows) (issued : priorRows)
    (block : Fin (v).receiver.blocks) (node:Fin (r).nodes) (arg:Fin (r).args)
    (rh:Fin (setup).placement.newHosts) (rg:Fin (setup).placement.groups)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (choice:∀f:Fin 7,OrdinalRead u ready small actors ((v).operandOrdinal (u).operand f arg block node))
    (live:0<(v).receiver.lanes) (bus:(u).operand.coeff*(v).receiver.lanes≤w)
    (lane:(v).receiver.signedBits*(v).receiver.lanes≤w)
    (masked:actorAt=0) (axis:Fin 3) :
    ((choice (page axis)).amount rh rg).val=0 ∨ kept :=by
  classical
  obtain ⟨_,_,_,_,R,capture,selfAt,hRaw,sRaw,xCount,all⟩:=issued
  obtain ⟨menu,paid,published,enabled,regs,other⟩:=all block
  obtain ⟨hdr,x,X,sig,geo,dim,size,hub,fees,root,moved,matrix,signed,shared,returned⟩:=requests
  let name:=directory hRaw sRaw
  let data:=(u).menu.publicData sh start count io.hubs g (2^n) (liveAt block) (regsAt block) menu rfl
    block.val rh rg
  have mask:=enabled rh rg
  have inactive:(menu.active rh rg).val=0:=by
    simpa [DescentResetControlRegisters.Chart.enabled,masked] using mask
  have field : ((publicOperands (u).atlas (u).roots (u).menu.payload).oldConfig.header
      ((publicOperands (u).atlas (u).roots (u).menu.payload).basic data) 0).val=0:=by
    rw [(u).menu.public_header_register sh start count io.hubs g (2^n) (liveAt block) (regsAt block) menu rfl block.val rh rg 0]
    exact inactive
  have read:=returned block arg node menu published small choice live bus lane axis rh rg
  have zero (ignore:∀inside:rh.val<Fintype.card B.next.V,
      ¬(u).menu.keep ((setup).placement.shape (name ⟨rh.val,inside⟩))=true) :
      ((choice (page axis)).amount rh rg).val=0:=by
    let strips := fun j => DescentSixParty.PackedFlow.Channels.blockValues geo.cut ((r).before geo.size archived j)
      (cast (congrArg DescentGL.Layout dim) μ)
    let Y := (setup).assignedDigits geo.host geo.groups (u).bank.which X strips
    let entry := (r).outputID 1 (page axis) arg node
    let col := block.cast (u).operandBlocks
    have raw := (u).menu.inactive_span name Y entry col rh rg data (finProdFinEquiv (arg,node)) (page axis)
      (published.2.2.2.2.2.1 rh rg) (published.2.2.2.2.2.2 rh rg) field
    have empty := compact_unkept (setup).placement (setup).seven.batch (u).menu.keep name Y entry col rh rg ignore
    have hit := raw.trans (congrArg (fun x₀ => (x₀.val : Cell (setup).fieldBits)) empty)
    exact read.trans ((congrArg (fun x₀ : Cell (setup).fieldBits => ((x₀.val : Cell (v).receiver.valueBits).val)) hit).trans
      (by simp))
  by_cases active:∃hv:rh.val<Fintype.card B.next.V,(u).menu.keep ((setup).placement.shape (name ⟨rh.val,hv⟩))=true
  · obtain ⟨hv,h⟩:=active
    exact Or.inr ⟨hv,hRaw,sRaw,h⟩
  · exact Or.inl (zero (fun hv ok=>active ⟨hv,ok⟩))

theorem DateInputs.range_panel_outside
    (prepared : (rc).PreparedFits book) (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (dd:venue.degree=D) (cd:input.placement.cap=cap) (ready:(u).Ready)
    (archived:(r).Values) (μ:DescentGL.Layout (E).dim) (measured actors:Memory w)
    (inputMem : Memory w)
    (requests : amountRows) (issued : priorRows)
    (block : Fin (v).receiver.blocks) (node:Fin (r).nodes) (arg:Fin (r).args)
    (rh:Fin (setup).placement.newHosts) (rg:Fin (setup).placement.groups)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (choice:∀f:Fin 7,OrdinalRead u ready small actors ((v).operandOrdinal (u).operand f arg block node))
    (live:0<(v).receiver.lanes) (bus:(u).operand.coeff*(v).receiver.lanes≤w)
    (lane:(v).receiver.signedBits*(v).receiver.lanes≤w)
    (padding:Fintype.card B.next.V≤rh.val) (axis:Fin 3) :
    ((choice (page axis)).amount rh rg).val=0:=by
  have masked:=actualBit_outside B B.next.valid.host rh rg block padding
  rcases DateInputs.range_panel_inactive (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
    sceneRoom dd cd ready archived μ measured actors inputMem requests issued block node arg rh rg small choice
    live bus lane masked axis with hit|keep
  · exact hit
  · exact (Nat.not_lt_of_ge padding keep.choose).elim

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
