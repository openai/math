import OAI.Hierarchy.DescentTerminalOriginalHeaderDigits
import OAI.Hierarchy.DescentResetMountedHeader
import OAI.Hierarchy.DescentTerminalCubicRecordBits
import OAI.Hierarchy.DescentTerminalFixedSlices
import OAI.Hierarchy.DescentNamedFinalPointerArchive

namespace OAI
/-! # Four pointer headers in the mounted terminal date of the selected branch -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage issued

open DescentDatedPriorOperand
private theorem previousHeaderBank {L T : DescentDatedPriorOperand.Layout} (same : L = T) (base : ℕ) (field : Fin 4)
    (x : Fin L.blocks) (y : Fin T.blocks) (j : Fin L.operands) (arg : Fin T.operands)
    (sameBlock : x.val = y.val) (sameArg : j.val = arg.val) :
    previousBank L base x (DescentOperandStateBanks.page (field.castLE (by decide : 4 ≤ 7)) j) =
      previousBank T base y (DescentOperandStateBanks.page (field.castLE (by decide : 4 ≤ 7)) arg) := by
  subst T
  obtain rfl := Fin.ext sameBlock
  obtain rfl := Fin.ext sameArg
  rfl

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
variable (c : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
local notation "b" => issued X G S ordinary reset branch positive room shorten c
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "U" => Label G s Z rot
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent

variable {w : ℕ}
open DescentDatedAddressBook DescentTerminalFixedSlices DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup
variable {boardDegree:ℕ} (board : NonlinearExpanders.Graph n boardDegree) (dateAge dateDegree datePayload : ℕ)
    (ordinaryAt : ℕ→Dated.Ordinary) (operandLanes primitiveLanes : ℕ) (previousDate : StageVenueTail.Date)
    (priorAddress : ℕ→ℕ→Bank) (rosterBank : Bank) (datedFloor replayBase matrixTable : ℕ)
    (dateTag : ℕ→Bool) (dateRotation : ℕ→ℕ) (snapshots : DescentExteriorReplay.Snapshots k) (roleBase : ℕ)
    (datedMem : Memory w)

local notation "datePhase" => Phase.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateOut" => (datePhase).output
local notation "dateOrigin" => (datePhase).dateBase
local notation "dateMachine" => PhysicalReset.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  s Z operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
variable (dateInput :
  let machine := PhysicalReset.scheduled G S board k tail dateAge (W * piece) f g
    (max 1 (max reset.bitsR (C * reset.bitsR))) dateDegree datePayload ordinaryAt (RotorSpec.ofRates reset)
    (S.firstWidth G.b (W * piece)) (S.grainAt G.b (W * piece) 0) operandLanes primitiveLanes previousDate
    priorAddress rosterBank datedFloor
  machine.DateInputs (machine.stageStart datedFloor) w)

open Chronology DescentKernelHistory DescentPrimitivePalette DescentTerminalPointerDigits
open DescentBundleHistory DescentLocalArchiveOrder DescentTerminalChronologicalBooks
open DescentTerminalPointerIssue DescentDatedAddressBook DescentSIMDLookup DescentTerminalFixedSlices
open DescentDatedPriorOperand DescentPriorOperandColumns DescentPacking.PackedMatch.Local.Stage
open DescentLocalPrivateNames
local notation "ports" => DatePorts.reset dateMachine ((dateMachine).stageStart datedFloor) dateInput
local notation "arch" => Branch.archive X G S b positive
local notation "schema" => Branch.bundleShape X G S b positive (le_max_left 1 (max reset.bitsR (C*reset.bitsR)))
local notation "order" => Branch.localNodes X G S b positive
local notation "actualPtr" => Reached.argumentPointer (b).target (arch).bit order schema positive
  (fun z=>z.1.val) (dateOut).argumentSlots
local notation "ptrBits" => DescentOperandWidth.recordBits G S k tail R 3 p
local notation "widths" => (⟨Nat.clog 2 (nodeCap+1),Nat.clog 2 (cap+1),fun _=>ptrBits,some nodeCap⟩ : Widths)
variable (past : Memory w) (capture size : ℕ) (source : ℕ→ℕ)
    (mount : RoleMount w roleBase replayBase)
local notation "mounted_" => mount.phase.image (DescentLowCountBook.output capture source past size)
local notation "nodeName" v:arg => ((order) v).toEmbedding.trans Fin.valEmbedding
local notation "recipe_" v:arg => ((schema).sites v).recipe positive
local notation "location" => (dateOut).terminalPointers dateOrigin

set_option maxHeartbeats 1200000 in
/-- Read the terminal pointer pages after the actual low-count capture and role-table mount.
Both writes preserve the original archived header at each live local argument. -/
theorem final_operand_headers_of_width
    (reached : FinalPointerArchive X G S ordinary reset branch positive room shorten w c ports past)
    (sizes : DescentOperandWidth.recordBits G S k tail R dateDegree p=ptrBits)
    (early : capture+size≤dateOrigin) (done_ : (dateOut).finalEnd dateOrigin≤roleBase)
    (space : (dateOut).metadataEnd dateOrigin<2^w)
    (single : chunks (dateOut).receiver.groups (dateOut).receiver.lanes=1)
    (wide : ((dateOut).nodeBits*(dateOut).nodes)*(dateOut).receiver.lanes≤w)
    (v : ((last).state c).graph.Site)
    (nn : Fintype.card (recipe_ v).Node≤nodeCap)
    (oldFits : ∀u,(recipe_ v).arity u≤(dateOut).argumentSlots)
    (a₀ : Slot (recipe_ v)) (f₀ : Fin 4) :
    (widths).nodeDigit ptrBits (DescentTerminalPointerIssue.row (recipe_ v) (nodeName v) nn a₀.1).val
      ((b).target.placement.pos v).1.val
      (mounted_ ((location f₀ (a₀.2.castLE (oldFits a₀.1)) ((b).target.placement.block v)).base+
        ((b).target.home v).val)).val=(actualPtr ⟨v,a₀.1⟩ a₀.2.val).header f₀:=by
  obtain ⟨places,label,flags,held⟩:=reached
  have capacity : (widths).nodeCapacity=some (ports).nodes:=rfl
  have scale (f : Fin 4) : (widths).pointer f=(ports).operandBits:=by
    change ptrBits=DescentOperandWidth.recordBits G S k tail R dateDegree p
    exact sizes.symm
  let arg:=a₀.2.castLE (oldFits a₀.1)
  have raw := DatePorts.ArchiveRead.header_at_original («ports»:=ports) (r:=(b).target) (B:=(arch).bit)
    (number:=order) (room:=places) (shape:=schema) (op:=rot) (label:=label) (pointer:=actualPtr) (flags:=flags)
    held positive widths capacity scale wide single v a₀.1 arg a₀.2.isLt f₀
  let host : Fin (dateOut).receiver.hosts := ⟨((b).target.home v).val,places.hosts v⟩
  have keep:=(dateOut).header_after_mount dateOrigin capture size source mount past early done_ space single
    f₀ arg ((b).target.placement.block v) host
  let digit (cell : Computability.VPVNP.BurstRAM.Word w) := (widths).nodeDigit ptrBits
    (DescentTerminalPointerIssue.row (recipe_ v) (nodeName v) nn a₀.1).val ((b).target.placement.pos v).1.val cell.val
  have axes : (ports).rangeLayout = (dateOut).rangeLayout := PhysicalReset.scheduled_range_layout
    G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot s Z operandLanes primitiveLanes
    previousDate priorAddress rosterBank datedFloor ((dateMachine).stageStart datedFloor) dateInput places.radix.symm
  let block := (Reached.NodeCells.coordinate (b).target v).2.2.cast (congrArg (2^·) places.radix)
  have sameBank := previousHeaderBank axes (ports).archive.arguments f₀ block ((b).target.placement.block v) arg arg rfl rfl
  have sameDigit := congrArg (fun (bank : Bank) => digit (past (bank.base + host.val))) sameBank
  exact (congrArg digit keep).trans (sameDigit.symm.trans raw)

theorem final_operand_headers
    (reached : FinalPointerArchive X G S ordinary reset branch positive room shorten w c ports past)
    (bounded : dateDegree≤DescentOperandWidth.raw S)
    (early : capture+size≤dateOrigin) (done_ : (dateOut).finalEnd dateOrigin≤roleBase)
    (space : (dateOut).metadataEnd dateOrigin<2^w)
    (single : chunks (dateOut).receiver.groups (dateOut).receiver.lanes=1)
    (wide : ((dateOut).nodeBits*(dateOut).nodes)*(dateOut).receiver.lanes≤w)
    (v : ((last).state c).graph.Site)
    (nn : Fintype.card (recipe_ v).Node≤nodeCap)
    (oldFits : ∀u,(recipe_ v).arity u≤(dateOut).argumentSlots)
    (a₀ : Slot (recipe_ v)) (f₀ : Fin 4) :
    (widths).nodeDigit ptrBits (DescentTerminalPointerIssue.row (recipe_ v) (nodeName v) nn a₀.1).val
      ((b).target.placement.pos v).1.val
      (mounted_ ((location f₀ (a₀.2.castLE (oldFits a₀.1)) ((b).target.placement.block v)).base+
        ((b).target.home v).val)).val=(actualPtr ⟨v,a₀.1⟩ a₀.2.val).header f₀ :=by
  exact final_operand_headers_of_width (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c) (board:=board)
    (dateAge:=dateAge) (dateDegree:=dateDegree) (datePayload:=datePayload) (ordinaryAt:=ordinaryAt)
    (operandLanes:=operandLanes) (primitiveLanes:=primitiveLanes) (previousDate:=previousDate)
    (priorAddress:=priorAddress) (rosterBank:=rosterBank) (datedFloor:=datedFloor) (dateInput:=dateInput)
    (w:=w) (replayBase:=replayBase) (roleBase:=roleBase) (past:=past) (capture:=capture) (size:=size) (source:=source) (mount:=mount) reached
    (DescentOperandWidth.recordBits_eq_cubic G S k tail R dateDegree p bounded)
    early done_ space single wide v nn oldFits a₀ f₀

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
