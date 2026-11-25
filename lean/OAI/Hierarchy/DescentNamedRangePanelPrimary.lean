import OAI.Hierarchy.DescentNamedPrimaryPacketRows
import OAI.Hierarchy.DescentCalendarInheritedMenuRange
import OAI.Hierarchy.DescentScheduledPrimaryDonorRead

namespace OAI
/-! # The three inherited span cells in the actual seven-field reset return -/
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
variable {F Pin : Type} [Field F] {d : ℕ} {abits : Pin→ℕ} {W : MarkedWorld F d Pin abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "namedSuccessor" => (a).successor
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
local notation "actorBase" => (namedSuccessor).middle.stop base₀
local notation "early" => (namedSuccessor).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (namedSuccessor).front.SceneRoom early ((namedSuccessor).issuedScene base₀ older) w)
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
local notation "U" => (namedSuccessor).actor

open DescentSortedRoster
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (namedSuccessor).setup
local notation "r" => (setup).retained
local notation "coarse" => (T).commonDepth
local notation "span" => (Z).k-coarse
local notation "field" => (namedSuccessor).middle.rootField

local notation "ctrl" => (namedSuccessor).controlRegisters
local notation "controlStart" => (namedSuccessor).controlFloor base₀
local notation "liveAt" x:arg => (ctrl).live controlStart (x:Fin (namedSuccessor).receiver.blocks).val
local notation "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (namedSuccessor).receiver.blocks).val
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
    (now : NodeOrder.All after_) (old : NodeOrder.All oldA.bit)
    (slotAt : DatePorts.slotAt ports B.next after_ newNum places block node rack group=some now)
    (source : resetOrigin B hp whole oldA now=Sum.inl old) (size : HH*rows=(setup).placement.sparse)
local notation "term" => (T).home old.1
local notation "sourceHost" => B.frame.host.symm ((T).code term).1
local notation "carrier" => idx sourceHost
local notation "rootHi" => (Z).rootBlock T (.inr term)
local notation "cutEq" => (show (r).cut=coarse from B.commonDepth.symm)
local notation "nativeHi" => (rootHi).cast (congrArg (2^·) cutEq).symm
local notation "dirs" => fun j : Fin (Fintype.card B.next.V)=>((Z).rawAtIndex T rank j).cast size
open DescentBundleHistory DescentOperandStateBanks DescentRotorWindowArchive DescentLocalPrivateNames
open DescentPlainTerminal DescentChosenRouter DescentResetTrunks DescentSixParty.ResetInput
open DescentSixParty.ClosedReset.Window
variable {R:ℕ} (one:1≤R) (posUnit:0<(Z).unit) (widthBound:max 1 (max (Z).width (C*(Z).width))≤R)
    (shape:WorldShape p R oldA.bit) (pin:Pin→ℕ)
local notation "split_" => shape.granular B.count (z*G.b) B.fit hp (B.unit ▸ posUnit) (B.unit ▸ whole)
local notation "unitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=B.reset.unit/p*p)
local notation "installed_" => reentryWorldShape split_ B.reset B.terminals (DescentOrderedReset.grains W B.count B.order)
  _ hp unitEq (resetMenu B) one widthBound
local notation "currentShape" => WorldShape.follow hp posUnit whole B.reblock B.cuts installed_
local notation "requestsAt" => DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom degreeAt capAt
variable (ready:(u).Ready) (archived:(r).Values) (μ:DescentGL.Layout (E).dim) (measured actors:Memory w)
    (requests:(requestsAt) ready archived μ measured actors) (won:HEq μ B.frame.basis)
    (total:(r).high+(r).low=cc+k) (oldBlocks:(r).blocks=2^k) (oldGroups:(r).groups=S.groupCount age)
    (oldRoom:∀v,Fintype.card (oldA.bit.recipe v).Node≤(r).previousNodes)
    (oldArgs:∀v n₁,((shape.sites v).recipe hp).arity n₁≤(r).previousArgs)
    (newRoom:Fintype.card ((after_).recipe now.1).Node≤(r).nodes)
    (original:∀(geo:(setup).MovementShape)(dim:(E).dim=(r).high+(r).low),
      PrimaryDonorRead B setup oldA num shape hp pin total cutEq oldBlocks oldGroups geo.size geo.cut input.valid.host
        oldRoom oldArgs (cast (congrArg DescentGL.Layout dim) μ) archived)
    (x₀:Fin (namedSuccessor).receiver.blocks) (arg:Fin (r).args) (newNode:Fin (r).nodes)
    (rh:Fin (setup).placement.newHosts) (rg:Fin (setup).placement.groups)
    (blockAt:x₀.val=block.val) (nodeAt:newNode.val=node.val) (hostAt:rh.val=rack.val) (groupAt:rg.val=group.val)
    (fieldRoom:(r).bits≤(setup).fieldBits) (outRoom:(r).bits≤(namedSuccessor).receiver.valueBits)
    (values:(deck x₀).Values (setup).placement.newHosts (setup).placement.groups)
    (published:(u).PublicValuesRead ready actors (x₀.cast (u).operandBlocks) rfl dirs values)
    (small:2*(namedSuccessor).receiver.candidates<2^(namedSuccessor).receiver.queryBits)
    (choice:∀a₀:Fin 7,OrdinalRead u ready small actors ((namedSuccessor).operandOrdinal (u).operand a₀ arg x₀ newNode))
    (live:0<(namedSuccessor).receiver.lanes) (bus:(u).operand.coeff*(namedSuccessor).receiver.lanes≤w)
    (lane:(namedSuccessor).receiver.signedBits*(namedSuccessor).receiver.lanes≤w)

include requests won slotAt source original newRoom blockAt nodeAt hostAt groupAt fieldRoom outRoom published live bus lane in
theorem DateInputs.range_panel_primary (axis:Fin 3) :
    ((choice (page axis)).amount rh rg).val=DescentRetainedRangeDigits.atSlot ((currentShape).sites now.1) now.2 arg.val axis:=by
  obtain ⟨hdr,x,X,sig,geo,dim,sz,hub,fees,root,moved,matrixRead,signed,controls,issued⟩:=requests
  obtain ⟨present,target,keep,priorHost,rootRow,atNode,packetWord,rowDegree,capped,bitsAt,fieldPos,
    stencilFits,ownerAt,priorAt,stencil⟩:=DateInputs.named_primary_packet_rows (B:=B)
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
    fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom degreeAt capAt
    measured hdr x X matrixRead oldA num hp whole ports places block node rack group now old slotAt source size
  have nodeEq:newNode=(newNum now.1 now.2).castLE newRoom:=Fin.ext (nodeAt.trans atNode)
  let basis:=cast (congrArg DescentGL.Layout dim) μ
  have chosen:HEq basis B.frame.basis:=(cast_heq _ μ).trans won
  let here:DescentNamedContact.Fibre (T).home ((T).home old.1):=⟨old.1,rfl⟩
  obtain ⟨rows_,arity_,header_,digits_⟩:=original geo dim old
  have alive:rh.val<Fintype.card B.next.V:=by simpa only [hostAt] using present
  let tok:=(setup).placement.shape (dirs ⟨rack.val,present⟩)
  have shapeEq:(setup).placement.shape (dirs ⟨rh.val,alive⟩)=tok:=by
    exact congrArg (fun j=> (setup).placement.shape (dirs j)) (Fin.ext hostAt)
  have host_:((setup).placement.previous (dirs ⟨rh.val,alive⟩)).cast geo.host=carrier:=by
    apply Fin.ext
    have point : (⟨rh.val,alive⟩:Fin (Fintype.card B.next.V))=⟨rack.val,present⟩:=Fin.ext hostAt
    rw [point]
    exact priorHost
  have coarse_:(finProdFinEquiv (rg,x₀.cast (u).operandBlocks)).cast geo.groups=nativeHi:=by
    apply Fin.ext
    simp only [Fin.val_cast,finProdFinEquiv_apply_val,groupAt,blockAt]
    rw [show (setup).placement.blocks=2^k from rfl]
    simpa only [Nat.mul_comm,Nat.add_comm] using rootRow
  have realWord:=issued x₀ arg newNode values published small choice live bus lane axis rh rg
  apply realWord.trans
  rw [nodeEq]
  apply calendar_inherited_span_cast (b:=B) («a»:=oldA) («early»:=num) (menu:=(u).menu) (total:=total)
    (axis:=cutEq) (blocks:=oldBlocks) (groups:=oldGroups) (size:=geo.size) (fits:=geo.cut) («L»:=basis) (won:=chosen)
    (room:=input.valid.host) (nodeRoom:=oldRoom) (hp:=hp) (whole:=whole) (one:=one) (posUnit:=posUnit)
    (widthBound:=widthBound) («sh»:=shape) (xx:=now) (yy:=old) (origin:=source) (which:=(u).bank.which) (window:=X)
    («shape»:=tok) («input»:=archived) (word:=x.stencil carrier rootHi) (counts:=rows_) (nextRoom:=newRoom)
    (namesAt:=dirs) (hostEq:=geo.host) (groupEq:=geo.groups) (block:=x₀.cast (u).operandBlocks) (rack:=rh)
    (g₁:=rg) (alive:=alive) (arg:=arg) (f₀:=axis) (compactShape:=shapeEq) (compactHost:=host_)
    (compactGroup:=coarse_) (keep:=keep) (outBits:=(namedSuccessor).receiver.valueBits) (outRoom:=outRoom)
    (enough:=fieldRoom) (fitsArgs:=oldArgs old.1 old.2) (arityRead:=arity_ here old.2)
  · simp only [finCongr_apply,Fin.cast_cast] at ownerAt ⊢
    exact ownerAt
  · simp only [finCongr_apply,Fin.cast_cast] at priorAt ⊢
    exact priorAt
  · exact stencil
  · intro j _ active
    exact digits_ here ⟨old.2,⟨j.val,active⟩⟩ axis

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
