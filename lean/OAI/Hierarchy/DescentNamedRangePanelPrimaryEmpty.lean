import OAI.Hierarchy.DescentNamedPrimaryEmptyDigits
import OAI.Hierarchy.DescentPaidEmptySpan

namespace OAI
/-! # Physical paid operand words at every absent scalar on an active primary -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open DescentPacking.PackedMatch.Local.Stage DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "HH" => S.hostSize age

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor

open DescentSortedRoster
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (v).setup
local notation "r" => (setup).retained

local notation "ctrl" => (v).controlRegisters
local notation "controlStart" => (v).controlFloor base₀
local notation "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
local notation "deck" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (liveAt x) (regsAt x)

open DescentSixParty.Chronology.DatePorts
open DescentLocalArchiveOrder DescentKernelHistory DescentPrimitivePalette DescentRetainedRangeDigits
open DescentFallbackShapeTable DescentRelativeContacts DescentIssuedFallbackPanel
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
variable (oldA : Archive W) (num : Local oldA.bit) (hp : 0<p) (whole : p∣(Z).unit)
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "newNum" => DescentLocalArchiveOrder.reset B p hp whole oldA num
variable (ports : DatePorts) (places : DatePorts.RangeRoom ports B.next after_)
    (block : Fin (2^ports.venue.k)) (node : Fin ports.nodes) (rack : Fin ports.operandHosts) (group : Fin ports.venue.groups)
variable (present:rack.val<Fintype.card B.next.V)
    (absent:DatePorts.slotAt ports B.next after_ newNum places block node rack group=none)
    (size:HH*rows=(setup).placement.sparse)
local notation "dirs" => fun j:Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size
local notation "tok" => (setup).placement.shape (dirs ⟨rack.val,present⟩)

open DescentRetainedRangeDigits
local notation "requestsAt" => DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom degreeAt capAt
variable (ready:(u).Ready) (archived:(r).Values) (μ:DescentGL.Layout (E).dim) (measured actors:Memory w)
    (requests:(requestsAt) ready archived μ measured actors) (won:HEq μ B.frame.basis)
    (total:(r).high+(r).low=cc+k) (oldBlocks:(r).blocks=2^k) (oldGroups:(r).groups=S.groupCount age)
    (original:∀(geo:(setup).MovementShape)(dim:(E).dim=(r).high+(r).low),
      OriginalRootCounts (input:=input) (oldA:=oldA) (r) archived geo.size geo.cut
        (cast (congrArg DescentGL.Layout dim) μ) input.valid.host oldGroups oldBlocks)
    (x₀:Fin (v).receiver.blocks) (arg:Fin (r).args) (newNode:Fin (r).nodes)
    (rh:Fin (setup).placement.newHosts) (rg:Fin (setup).placement.groups)
    (blockAt:x₀.val=block.val) (nodeAt:newNode.val=node.val) (hostAt:rh.val=rack.val) (groupAt:rg.val=group.val)
    (values:(deck x₀).Values (setup).placement.newHosts (setup).placement.groups)
    (published:(u).PublicValuesRead ready actors (x₀.cast (u).operandBlocks) rfl dirs values)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (choice:∀a₀:Fin 7,OrdinalRead u ready small actors ((v).operandOrdinal (u).operand a₀ arg x₀ newNode))
    (live:0<(v).receiver.lanes) (bus:(u).operand.coeff*(v).receiver.lanes≤w)
    (lane:(v).receiver.signedBits*(v).receiver.lanes≤w)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
include total absent requests won original blockAt nodeAt hostAt groupAt published live bus lane in
theorem DateInputs.range_panel_primary_empty (keep:(u).menu.keep tok=true) (axis:Fin 3) :
    ((choice (page axis)).amount rh rg).val=0:=by
  obtain ⟨hdr,x,windows,sig,geo,dim,sz,hub,fees,root,moved,matrixRead,signed,controls,issued⟩:=requests
  let basis:=cast (congrArg DescentGL.Layout dim) μ
  have basisAt:HEq basis B.frame.basis:=(cast_heq _ μ).trans won
  have empty_:=DateInputs.decoded_primary_empty (F:=F) (X:=X) (d:=d) (abits:=abits) (W:=W)
    (G:=G) (q:=q) (ε:=ε) (S:=S) (k:=k) (age:=age) (z:=z) (wire:=wire) (hist:=hist)
    (D:=D) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (cut:=cut) (tail:=tail) (p:=p)
    (input:=input) (ctl:=ctl) (B:=B)
    (drift:=drift) (degree:=degree) (payload:=payload) (e:=e) (previous:=previous) (M:=M)
    (nextM:=nextM) (oldLanes:=oldLanes) (primitiveLanes:=primitiveLanes) (printedBits:=printedBits)
    (venue:=venue) (io:=io) (floor:=floor) (w:=w) (fitsStencil:=fitsStencil) (fitsSigned:=fitsSigned)
    (fitsCut:=fitsCut) (count:=count) (previousMeta:=previousMeta) (previousArguments:=previousArguments)
    (initial:=initial) (prepared:=prepared) (sceneRoom:=sceneRoom) (degreeAt:=degreeAt) (capAt:=capAt)
    (oldA:=oldA) (num:=num) (hp:=hp) (whole:=whole) (ports:=ports) (places:=places)
    (block:=block) (node:=node) (rack:=rack) (group:=group) (present:=present) (absent:=absent) (size:=size)
    (measured:=measured) (hdr:=hdr) (xs:=x) (windows:=windows) (matrixRead:=matrixRead) (geo:=geo)
    (basis:=basis) (won:=basisAt) (oldValues:=archived) (total:=total) (groupSize:=oldGroups) (blockSize:=oldBlocks)
    (population:=original geo dim) (operand:=arg) (slot:=newNode) (rg:=rg) (x₀:=x₀.cast (u).operandBlocks)
    (nodeAt:=nodeAt) (groupAt:=groupAt) (blockAt:=blockAt) keep axis
  have emitted:=issued x₀ arg newNode values published small choice live bus lane axis rh rg
  have inside:rh.val<Fintype.card B.next.V:=by rw [hostAt];exact present
  have same:(⟨rh.val,inside⟩:Fin (Fintype.card B.next.V))=⟨rack.val,present⟩:=Fin.ext hostAt
  apply DateInputs.paid_empty_span (menu:=(u).menu) (alive:=inside) emitted
  · rw [same];exact keep
  · rw [same];exact empty_

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
