import OAI.Hierarchy.DescentNamedRelayRangeRead
import OAI.Hierarchy.DescentNamedTerminalMenu
import OAI.Hierarchy.DescentRelayVacantCoordinates
import OAI.Hierarchy.DescentRelayOccupiedLocation
import OAI.Hierarchy.DescentCapturedRelayRange

namespace OAI
/-! # The original range output for an occupied or padded relay node -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
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
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
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
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
  (sceneRoom : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "HH" => S.hostSize age

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor

open DescentSortedRoster
local notation:max "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
open DescentSixParty.ClosedReset.Window DescentOperandRootPull DescentSixParty.PackedFlow.Channels
local notation "setup" => (v).setup
local notation "r" => (setup).retained

local notation "ctrl" => (v).controlRegisters
local notation "controlStart" => (v).controlFloor base₀
local notation:max "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation:max "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)

open DescentSixParty.Chronology DescentSixParty.Chronology.DatePorts
open DescentLocalArchiveOrder DescentKernelHistory DescentPrimitivePalette DescentRetainedRangeDigits
open DescentFallbackShapeTable DescentRelativeContacts DescentIssuedFallbackPanel
set_option hygiene false
local notation "im_" => imageOf degreeAt capAt
local notation "after_" => (resetArchive B p hp whole oldA).bit
local notation "newNum" => DescentLocalArchiveOrder.reset B p hp whole oldA num
open DescentBundleHistory DescentOperandStateBanks DescentRotorWindowArchive DescentLocalPrivateNames
open DescentPlainTerminal DescentChosenRouter DescentResetTrunks DescentSixParty.ResetInput
open DescentSixParty.ClosedReset.Window
open DescentResetPublicOperandBook DescentPaidResidentCount DescentPackedZip
local notation "split_" => shape.granular B.count (z*G.b) B.fit hp (B.unit ▸ posUnit) (B.unit ▸ whole)
local notation "unitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=B.reset.unit/p*p)
local notation "installed_" => reentryWorldShape split_ B.reset B.terminals (DescentOrderedReset.grains W B.count B.order)
  _ hp unitEq (resetMenu B) one widthBound
local notation "currentShape" => WorldShape.follow hp posUnit whole B.reblock B.cuts installed_
local notation "requestsAt" => DateInputs.RangeRequestsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom degreeAt capAt
local notation:max "sourceRowsAt" ready:arg m:arg μ:arg measured:arg actors:arg => DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared sceneRoom degreeAt ready m capAt μ measured actors
local notation "cfg" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation:max "K" batch:arg => publicOperandConfig B (setup).rotorBits (setup).queryBits M batch ((Z).unit/p)
    S.retainedNodes (S.retainedArgumentsAt G drift) p
local notation "oldWorld" => W.granular B.count (z*G.b) B.fit
local notation:max "target" t:arg => (blocks B).dst (trunkParent B t)
local notation "loc" => operandLocation B (x₀.cast (show (v).receiver.blocks=2^k from rfl))
  (rh.cast (show (setup).placement.newHosts=(v).sheets.hosts from rfl))
  (rg.cast (show (setup).placement.groups=S.groupCount (age+1) from rfl))
local notation "dateConfig" => DateInputs.fromNamed_public_socket_config (B:=B) accepted drift degree payload e previous
  M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom degreeAt capAt grainAt
local notation:max "amountAt" menu:arg published:arg batch:arg eqn:arg graphAt:arg axis:arg amount:arg => DateInputs.right_range_amount (B:=B) drift
  degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
  count previousMeta previousArguments initial prepared sceneRoom degreeAt capAt size ready archived μ measured actors
  requests x₀ arg newNode rh rg menu published small choice live bus lane batch eqn graphAt axis amount

set_option hygiene true
include accepted in
theorem DateInputs.range_panel_relay
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (oldA : Archive W) (num : Local oldA.bit) (hp : 0<p) (whole : p∣(Z).unit)
    (ports : DatePorts) (places : DatePorts.RangeRoom ports B.next after_)
    (block : Fin (2^ports.venue.k)) (node : Fin ports.nodes) (rack : Fin ports.operandHosts) (group : Fin ports.venue.groups)
    {R:ℕ} (one:1≤R) (posUnit:0<(Z).unit) (widthBound:max 1 (max (Z).width (C*(Z).width))≤R)
    (shape:WorldShape p R oldA.bit)
    (grainAt:z=S.grainAt G.b p (age+1)) (ready:(u).Ready) (archived:(r).Values) (μ:DescentGL.Layout (E).dim)
    (m measured actors:Memory w) (requests:(requestsAt) ready archived μ measured actors)
    (original:sourceRowsAt ready m μ measured actors) (size:HH*rows=(setup).placement.sparse)
    (x₀:Fin (v).receiver.blocks) (arg:Fin (r).args) (newNode:Fin (r).nodes)
    (rh:Fin (setup).placement.newHosts) (rg:Fin (setup).placement.groups)
    (blockAt:x₀.val=block.val) (nodeAt:newNode.val=node.val) (hostAt:rh.val=rack.val) (groupAt:rg.val=group.val)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (choice:∀j:Fin 7,OrdinalRead u ready small actors ((v).operandOrdinal (u).operand j arg x₀ newNode))
    (live:0<(v).receiver.lanes) (bus:(u).operand.coeff*(v).receiver.lanes≤w)
    (lane:(v).receiver.signedBits*(v).receiver.lanes≤w)
   (now:NodeOrder.All after_) (edge:(oldWorld).graph.Edge)
    (slotAt:DatePorts.slotAt ports B.next after_ newNum places block node rack group=some now)
    (origin:resetOrigin B hp whole oldA now=.inr (.inl edge)) (elapsed:0<age) (sorted:SourceSorted W input.order)
    (axis:Fin 3) :
    ((choice (page axis)).amount rh rg).val=atSlot ((currentShape).sites now.1) now.2 arg.val axis:=by
  obtain ⟨spot,numAt⟩:=relay_occupied_location B hp whole oldA ports newNum places block node rack group now
    slotAt rh hostAt edge origin
  have blockEq : x₀.cast (show (v).receiver.blocks=2^k from rfl) =
      block.cast (congrArg (2^·) places.radix.symm) := Fin.ext blockAt
  have groupEq : rg.cast (show (setup).placement.groups=S.groupCount (age+1) from rfl) =
      group.cast places.groups.symm := Fin.ext groupAt
  have location : loc=some (target ((T).home ((oldWorld).graph.dst edge))) :=
    (congrArg₂ (fun x g₀ => operandLocation B x rh g₀) blockEq groupEq).trans spot
  obtain ⟨boardAt,baseShape⟩:=dateConfig
  have calibrated:cfg=K ((Z).unit/p):=by rwa [←funded_units B accepted grainAt] at baseShape
  obtain ⟨menu,posted,active,capacity,recorded,tag,tagRead,kind⟩:=DateInputs.relay_observation_at_slot (B:=B) accepted
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned
    fitsCut count previousMeta previousArguments initial prepared sceneRoom degreeAt ready m capAt grainAt μ measured actors
    original x₀ size calibrated rfl rfl rfl rh rg edge location
  let printed:=(u).menu.publicData sh start count io.hubs g (2^n) (liveAt x₀) (regsAt x₀)
    menu rfl x₀.val rh rg
  let row:=Config.relabel calibrated B.dimension.symm printed
  let arg₁:=arg.cast (congrArg (fun c:Config=>c.args) calibrated)
  let node₁:=newNode.cast (congrArg (fun c:Config=>c.nodes) calibrated)
  have value:=OriginalRelayRows.range_digit (M:=M) B hp one posUnit whole widthBound oldA shape num now edge origin
    arg₁ node₁ row axis (setup).fieldBits (nodeAt.trans numAt) active capacity ⟨tag,tagRead,kind⟩ recorded elapsed sorted
  have bounded:atSlot ((currentShape).sites now.1) now.2 arg.val axis≤1:=by
    rw [relay_range_at B hp one posUnit whole widthBound oldA shape now edge origin]
    fin_cases axis <;> split <;> decide
  have outRoom : 1<2^(v).receiver.valueBits := DescentOperandWidth.bitOffset G S (i:=1) hp
  have fieldRoom : 1<2^(setup).fieldBits := outRoom.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))
  exact amountAt menu posted ((Z).unit/p) calibrated boardAt axis _
    active ⟨tag,tagRead,_,kind⟩ value (bounded.trans_lt fieldRoom) (bounded.trans_lt outRoom)

local notation:max "realRelay" t:arg => B.reblock.destination (((Z).resetNames T).symm (.inl (true,t)))
local notation "batches" => ResetInput.calendarLanes S G.b (age+1)
local notation "field" => (setup).rotorBits
local notation "query" => (setup).queryBits
local notation:max "tagT" t:arg => (Z).localShape T (target t).1.2
local notation:max "seenSnap" ss:arg => DateInputs.relay_snapshot (B:=B) (drift:=drift) (degree:=degree)
  (payload:=payload) (e:=e) (previous:=previous) (M:=M) (nextM:=nextM) (oldLanes:=oldLanes)
  (primitiveLanes:=primitiveLanes) (printedBits:=printedBits) (venue:=venue) (io:=io) (floor:=floor) (p:=p) ss

include accepted in
theorem DateInputs.range_panel_relay_vacant
    (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (oldA : Archive W) (num : Local oldA.bit) (hp : 0<p) (whole : p∣(Z).unit)
    (ports : DatePorts) (places : DatePorts.RangeRoom ports B.next after_)
    (block : Fin (2^ports.venue.k)) (node : Fin ports.nodes) (rack : Fin ports.operandHosts) (group : Fin ports.venue.groups)
    (grainAt:z=S.grainAt G.b p (age+1)) (ready:(u).Ready) (archived:(r).Values) (μ:DescentGL.Layout (E).dim)
    (m measured actors:Memory w) (requests:(requestsAt) ready archived μ measured actors)
    (original:sourceRowsAt ready m μ measured actors) (size:HH*rows=(setup).placement.sparse)
    (x₀:Fin (v).receiver.blocks) (arg:Fin (r).args) (newNode:Fin (r).nodes)
    (rh:Fin (setup).placement.newHosts) (rg:Fin (setup).placement.groups)
    (blockAt:x₀.val=block.val) (nodeAt:newNode.val=node.val) (hostAt:rh.val=rack.val) (groupAt:rg.val=group.val)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (choice:∀j:Fin 7,OrdinalRead u ready small actors ((v).operandOrdinal (u).operand j arg x₀ newNode))
    (live:0<(v).receiver.lanes) (bus:(u).operand.coeff*(v).receiver.lanes≤w)
    (lane:(v).receiver.signedBits*(v).receiver.lanes≤w)
   (t:(Z).Fallback) (inside:rack.val<Fintype.card B.next.V)
    (here:occupies B.next.placement (Equiv.refl _) B.next.vertex ⟨rack.val,inside⟩
      (group.cast places.groups.symm) (block.cast (congrArg (2^·) places.radix.symm)) (realRelay t))
    (empty:DatePorts.slotAt ports B.next after_ newNum places block node rack group=none) (axis:Fin 3) :
    ((choice (page axis)).amount rh rg).val=0:=by
  obtain ⟨hs,gs,bs⟩:=DatePorts.relay_vacant_coordinates B ports places.groups.symm places.radix.symm
    block rack group inside t here
  have placeX:x₀=(target t).2:=Fin.ext (blockAt.trans bs.symm)
  have placeH:rh=((denseOrder B) (target t).1.2).castLE B.next.valid.host:=Fin.ext (hostAt.trans hs.symm)
  have placeG:rg=(target t).1.1:=Fin.ext (groupAt.trans gs.symm)
  subst x₀
  subst rh
  subst rg
  obtain ⟨hRaw,sRaw,xCount,menu,paid,published,hdr,xs,held,data⟩:=DateInputs.fromNamed_terminal_menu (B:=B) accepted
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned
    fitsCut count previousMeta previousArguments initial prepared sceneRoom degreeAt ready m capAt grainAt μ measured actors
    original t
  obtain ⟨packetT,«on»,tagRead,kind⟩:=data
  have boardAt:=dateConfig.1
  let cfgAt:=dateConfig.2
  let snap:=DescentPaidResidentCount.Reset.root_snapshot B input.valid.host (im_).receiver (im_).book (im_).prepared measured hdr xs
  let arg₁:=arg.cast (congrArg (fun c:Config=>c.args) cfgAt)
  let node₁:=newNode.cast (congrArg (fun c:Config=>c.nodes) cfgAt)
  let row:=Config.relabel cfgAt B.dimension.symm ((u).menu.publicData sh start count io.hubs g (2^n)
    (liveAt (target t).2) (regsAt (target t).2) menu paid (target t).2.val
    (((denseOrder B) (target t).1.2).castLE B.next.valid.host) (target t).1.1)
  have zero:=relay_ghost_span («field»:=field) («query»:=query) (lanes:=M) («batches»:=batches) (split:=(Z).unit/p)
    (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) (grain:=p)
    B input.valid.host Fin.valEmbedding (seenSnap snap) hp whole oldA num ports places block node rack group inside
    t row (tagT t) «on» tagRead kind packetT node₁ arg₁ (setup).fieldBits (some (page axis)) nodeAt here empty
  exact DateInputs.right_range_amount (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    degreeAt capAt size ready archived μ measured actors requests _ arg newNode _ _ menu published small choice live
    bus lane batches cfgAt boardAt axis 0 «on» ⟨tagT t,tagRead,_,kind⟩ zero (Nat.two_pow_pos _) (Nat.two_pow_pos _)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
