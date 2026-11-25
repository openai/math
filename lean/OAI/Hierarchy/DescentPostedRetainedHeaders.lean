import OAI.Hierarchy.DescentNamedRetainedHeaderRead
import OAI.Hierarchy.DescentNamedPrimaryPacketRows
import OAI.Hierarchy.DescentRegisteredRetainedSlot
import OAI.Hierarchy.DescentAcquiredPrimaryDonors
import OAI.Hierarchy.DescentOriginalPrimaryLimits
import OAI.Hierarchy.DescentIssuedResetShape
import OAI.Hierarchy.DescentInitialArgumentCapacity
import OAI.Hierarchy.DescentFundedJobCalendar
import OAI.Hierarchy.DescentNamedPanelPublicCapacity

namespace OAI
/-! The registered argument pointer of every inherited node on the same issued operand panel. -/
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
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "namedReset" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "namedSuccessor" => (namedReset).successor
local notation "start" => (namedReset).stageStart floor
local notation "base₀" => (namedReset).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (namedReset).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (namedReset).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (namedReset).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (namedSuccessor).middle.stop base₀
local notation "early" => (namedSuccessor).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (namedSuccessor).front.SceneRoom early ((namedSuccessor).issuedScene base₀ older) w)
local notation "dateInput" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "entry₀" => (namedReset).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "C₀" => (namedSuccessor).setup
open DescentLocalArchiveOrder DescentKernelHistory DescentBundleHistory DescentPrimitivePalette
open DescentGL DescentFallbackPeriod.Projected DescentCommonHost
open DescentDatedPriorOperand DescentRetainedRangeDigits DescentLocalPrivateNames
open DescentResetOperandSetup DescentPacking.PackedMatch.Local.Stage DescentRetainedPrivateSlotBook
open DescentRetainedResetPinPointer DescentSixParty.Chronology DescentSixParty.ClosedReset DescentSixParty.ClosedReset.Window
open scoped BigOperators
local notation "K" => (C₀).retained
local notation "Rports" => DatePorts.reset namedReset start dateInput
local notation "panels" => DateInputs.OperandPanelsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
local notation "menus" => DateInputs.PublicOperandRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
variable [Fintype X] {R:ℕ} (oldA:Archive W) (oldNum:Local oldA.bit) (shape:WorldShape p R oldA.bit)
    (hp:0<p) (one:1≤R) (unitPos:0<(Z).unit) (whole:p∣(Z).unit)
    (widthBound:max 1 (max (Z).width (C*(Z).width))≤R) (pin:X→ℕ)
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "order_" => DescentLocalArchiveOrder.reset B p hp whole oldA oldNum
local notation "shape₁" => reset_shape_at hp one B oldA shape unitPos whole widthBound
variable (ready:(dateInput).Ready) (actorMem:Memory w) (small:2*(namedSuccessor).receiver.candidates<2^(namedSuccessor).receiver.queryBits)
    (axes:(Rports).rangeLayout=(namedSuccessor).rangeLayout) (choices:∀i,DatePorts.OrdinalRead (dateInput) ready small actorMem i)
    (places:DatePorts.RangeRoom Rports B.next after_)
    (previousCapacity:∀v₀,Fintype.card (oldA.bit.recipe v₀).Node≤(K).previousNodes)
    (previousArgs:∀v₀ n₀,((shape.sites v₀).recipe hp).arity n₀≤(K).previousArgs)
    (arity:∀v₀ n₀,(((shape₁).sites v₀).recipe hp).arity n₀≤(Rports).argumentsPerNode)
variable (degreeAt:venue.degree=D) (capAt:input.placement.cap=cap)
    (height:0<S.height) (base:G.b≤2^S.capGain) (grainAt:z=S.grainAt G.b p (age+1))
    (oldValues:(K).Values) (m:Memory w)
    (held:panels degreeAt capAt ready m oldValues)
    (reached:(dateInput).ThroughActors ((entry₀).image m) actorMem)
    (public_:menus ready actorMem)
local notation "geom_" => S.previousGeometry G k tail drift degree p age payload (prior_).nodes
    (prior_).arguments (prior_).operandLanes ctl.base ctl.radix B.age
local notation "total_" => (geom_).1
local notation "axis_" => (B.commonDepth.symm:(K).cut=(T).commonDepth)
local notation "hostRoom" => (input.valid.host:Fintype.card input.V≤(K).hosts)
variable (previousRows:∀(G₀:(C₀).MovementShape) (basis:DescentGL.Layout ((K).high+(K).low)),
    HEq basis B.frame.basis→Window.PrimaryDonorRead B (C₀) oldA oldNum shape hp pin total_ axis_ rfl rfl
      G₀.size G₀.cut hostRoom previousCapacity previousArgs basis oldValues)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
omit [Fintype X] in
include arity degreeAt capAt height base grainAt accepted held reached public_ previousRows in
theorem DateInputs.registered_retained_headers :
    DatePorts.SevenOriginHeaders (dateInput) B.next after_ order_ places shape₁ hp pin ready small axes actorMem choices
      (resetOrigin B hp whole oldA) Sum.inl:=by
  obtain ⟨μ,measured,dst,won,_,_,scanned,published,requests,_,_,_,_,_,hx,hj,groupAt,_,aligned,live⟩:=held
  have ran:(dateInput).ThroughActors ((entry₀).image m) dst:=(DateInputs.classified_prefix (u:=dateInput) ready scanned published).1
  have same:dst=actorMem:=ProtocolRAM.exec_unique _ ((entry₀).image m) dst actorMem ran reached
  subst dst
  obtain ⟨hdr,xs,X₀,signed,geometry,dim,size_,hubWord,fee,source_,moved,matrix_,sign_,control,issued⟩:=requests
  let basis:DescentGL.Layout ((K).high+(K).low):=cast (congrArg DescentGL.Layout dim) μ
  have attained:HEq basis B.frame.basis:=HEq.trans (cast_heq ..) won
  let earlierRows:=previousRows geometry basis attained
  have oldSizes:=DescentSixParty.AtomSchedule.prior_capacity S G age p drift oldLanes primitiveLanes printedBits venue height base
  have stage:=named_successor G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor
  have fullRoom : (ResetOutput.fromBoard G S ctl.board k tail age p f g drift degree payload e previous M
      nextM C packet (prior_) base₀).finalEnd base₀ < 2^w := by
    rw [← stage]
    exact ready.full
  have limits:=Window.original_primary_limits B p drift degree payload e previous M nextM packet (prior_) base₀ w
    accepted grainAt height base (degreeAt.trans input.branch.symm) capAt oldSizes.1 oldSizes.2 fullRoom
  have lowOld:(K).donors=2^((Z).k-(T).commonDepth):=(dateInput).menu.donors.trans (congrArg (2^·) (calendar_residual B).symm)
  have capEq:(C₀).cable.cap=input.placement.cap:=(dateInput).menu.capacity.trans
    ((show (namedReset).c/2=cap by change (2*cap)/2=cap;omega).trans capAt.symm)
  have high_: (C₀).placement.groups*(C₀).placement.blocks=2^(T).commonDepth:=by
    rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix]
    rfl
  have blockAxis:(Rports).operandHosts=S.hostSize (age+1):=congrArg DescentDatedPriorOperand.Layout.hosts axes
  have ret:=DatePorts.registered_retained_capacity (dateInput) ready axes
  intro xb arg field rh rg node now slot formal prior source
  let mouthSlot:=DatePorts.registeredMouth after_ shape₁ hp now arg.val formal
  have capacity:Fintype.card ((after_).recipe now.1).Node≤(K).nodes:=(places.capacity now.1).trans_eq ret.2
  have argumentRoom:∀z₀,(((shape₁).sites now.1).recipe hp).arity z₀≤(K).args:=fun z₀=>(arity now.1 z₀).trans_eq ret.1
  let key:=reached_mouth _ ((order_ now.1).toEmbedding.trans (Fin.castLEEmb capacity)) argumentRoom mouthSlot
  let pos_ : Fin (K).nodes×Fin (K).args:=finProdFinEquiv.symm key
  let block:=xb.cast (congrArg DescentDatedPriorOperand.Layout.blocks axes)
  have payload_:=DateInputs.named_primary_packet_rows (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom degreeAt capAt measured hdr xs X₀ matrix_ oldA oldNum hp whole Rports places
    xb node rh rg now prior slot source size_
  obtain ⟨present,_,_,_,_,_,mx,rowDegree,rowCap,rowBits,rowPos,stencilFits,_⟩:=payload_
  obtain ⟨vals,publicRead,_⟩:=public_ size_ block
  obtain ⟨countWords,arityWords,headerWords,_⟩:=earlierRows prior
  apply DatePorts.registered_mouth_amount B.next after_ order_ shape₁ hp (dateInput) places ready axes small
    actorMem choices pin xb arg rh rg node now slot formal capacity argumentRoom _ field
  change ∀f₀:Fin 4,_
  apply DateInputs.registered_primary_header (F:=F) (Pin:=X) (d:=d) (abits:=abits) (W:=W) (G:=G) (q:=q) (ε:=ε) (S:=S) (k:=k) (age:=age) (z:=z) (wire:=wire) (hist:=hist) (D:=D) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (cut:=cut) (tail:=tail) (p:=p) (input:=input) (ctl:=ctl) (B:=B) (R:=R)
    (drift:=drift) (degree:=degree) (payload:=payload) (e:=e) (previous:=previous) (M:=M)
    (nextM:=nextM) (oldLanes:=oldLanes) (primitiveLanes:=primitiveLanes) (printedBits:=printedBits)
    (venue:=venue) (io:=io) (floor:=floor) (w:=w) (fitsStencil:=fitsStencil) (fitsSigned:=fitsSigned)
    (fitsCut:=fitsCut) (count:=count) (previousMeta:=previousMeta) (previousArguments:=previousArguments)
    (initial:=initial) (prepared:=prepared) (sceneRoom:=sceneRoom) (ok:=ready) (actorMem:=actorMem)
    (oldA:=oldA) (oldNum:=oldNum) (shape:=shape)
    (now:=now) (prior:=prior) (hp:=hp) (whole:=whole) (one:=one) (unitPos:=unitPos) (widthBound:=widthBound)
    (source:=source) (newArgs:=argumentRoom) (newRoom:=capacity) (mouth:=mouthSlot) (oldRoom:=previousCapacity)
    (oldArgs:=fun u₀=>previousArgs u₀.val) (oldValues:=oldValues) (pin:=pin)
    (hostEq:=geometry.host) (groupEq:=geometry.groups) (hostAxis:=blockAxis) (size_:=size_) (numHosts:=rfl)
    (rhAt:=rfl) (rgAt:=rfl) (blockAt:=rfl) (oldHosts:=hostRoom) (total:=total_) (axis:=axis_)
    (length:=geometry.size) (cutRoom:=geometry.cut) (basis:=basis) (attained:=attained)
    (arg:=pos_.2) (node:=pos_.1) (x₀:=block) (atArg:=rfl) (atNode:=rfl)
    (hx:=hx) (hj:=hj) (groupsAt:=groupAt) (aligned:=aligned)
    (measured:=measured) (hdr:=hdr) (xs:=xs) (matrixRead:=mx) (signed:=signed) (X:=X₀)
    (storedName:=fun _=>rfl) (oldStrips:=rfl) (oldBlocks:=rfl) (oldGroups:=rfl)
    (oldCodec:=by rw [stage]; exact limits.rootCodec) (lowOld:=lowOld) (hiOld:=high_) (signedRead:=sign_)
    (shelf:=by rw [stage]; exact limits.shelf)
    (chipRoom:=by rw [stage]; exact limits.chipRoom)
    (grainRoom:=by rw [stage]; exact limits.grainRoom) (rowDegree:=rowDegree) (rowCap:=rowCap)
    (rowBits:=rowBits) (rowPos:=rowPos) (stencilFits:=stencilFits) (cableRoom:=Window.original_cable_header_fits
       B after_ order_ shape₁ hp pin (K).args ⟨now.1,mouthSlot.1⟩ mouthSlot.2.val height grainAt base drift degree payload e
       previous M nextM packet (prior_) base₀)
    (small:=small)
    (choice:=fun f₀=>choices ((namedSuccessor).operandOrdinal (dateInput).operand f₀ pos_.2 block pos_.1))
    (read:=issued block pos_.2 pos_.1 vals publicRead) (observed:=publicRead)
    (archive:=live) (moved:=moved) (oldReads:=headerWords) (arities:=arityWords) (pop:=countWords)
    (digitRoom:=by rw [stage]; exact limits.digitRoom)
    (positive:=by rw [stage]; exact limits.positive)
    (output:=by rw [stage]; exact limits.output)
    (fieldRoom:=by rw [stage]; exact limits.fieldRoom)
    (oldWidth:=by rw [stage]; exact limits.oldWidth)
    (newWidth:=by rw [stage]; exact limits.newWidth)
    (alphabet:=by rw [stage]; exact limits.alphabet)
    (donorEq:=by rw [stage]; exact limits.donorEq)
    (unitEq:=by rw [stage]; exact limits.unitEq) (capEq:=capEq)
    (deg:=(show (C₀).cable.degree=input.placement.degree from degreeAt.trans input.branch.symm)) (atFee:=rfl)
    (degreeAt:=degreeAt) (slotAt:=slot) (allFees:=fee) (controls:=control)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
