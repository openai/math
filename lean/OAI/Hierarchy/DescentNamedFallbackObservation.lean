import OAI.Hierarchy.DescentNamedFallbackSocket
import OAI.Hierarchy.DescentNamedFreshMenus
import OAI.Hierarchy.DescentLocatedOperandRow
import OAI.Hierarchy.DescentFreshOperandObservation

namespace OAI
/-! # The actual fallback register, packet and donor readings at an original operand slot -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
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
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
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

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "group₁" => S.groupCount (age+1)
local notation "control" => (v).controlRegisters
local notation "first_" => (v).controlFloor base₀

local notation "C₀" => (v).setup
local notation:max "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation:max "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((U).directory actorBase).inverse
  ((U).depths actorBase) ((U).levels actorBase)

open DescentPaidResidentCount.Reset DescentResetPublicOperandBook
local notation:max "siteAt" side:arg t:arg q₀:arg => (⟨(side,.inr t),q₀⟩ : (Z).bank.Site)
local notation:max "place" side:arg t:arg q₀:arg => treeReceiver B (siteAt side t q₀)
local notation "rotor" => (v).setup.rotorBits
local notation "q₁" => (v).setup.queryBits
local notation "stages₁" => ResetInput.calendarLanes S G.b (age+1)
local notation "split" => (Z).unit/p
local notation:max "menuK" b:arg => publicOperandConfig B rotor q₁ M b split S.retainedNodes (S.retainedArgumentsAt G drift) p
local notation "K₁" => menuK split
local notation "config" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation:max "cfgEq" dd:arg cd:arg gr:arg => (DateInputs.fromNamed_public_socket_config (B:=B) accepted drift degree payload e
  previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
  previousArguments initial prepared sceneRoom dd cd gr).2
local notation:max "freshAt" row:arg side:arg t:arg q₀:arg => FreshObservation (p:=p) (field:=rotor) (query:=q₁) (lanes:=M)
  (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) B row (.inr (siteAt side t q₀))
local notation:max "treeRows" side:arg t:arg row:arg => FallbackRows (p:=p) (field:=rotor) (query:=q₁) (lanes:=M)
  (nodes:=S.retainedNodes) (args:=S.retainedArgumentsAt G drift) (grain:=p) B side t row
local notation:max "shapeAt" side:arg t:arg q₀:arg => (Z).localShape T ((Z).placed T ((Z).privateSiteAt T side (.inr t) q₀))

private theorem fallback_at_batch (batch : ℕ) (calibrated : batch=split) (paid : config=menuK batch)
    (shape : config=K₁) (raw : (config).Data n) (side : Bool) (t : (Z).Fallback)
    (q₀ : DescentContactTree.Physical.Site ((Z).placement.fallbackBook side t).height) :
    let row:=Config.relabel paid B.dimension.symm raw
    let header_:=(menuK batch).oldConfig.header ((menuK batch).basic row)
    treeRows side t row → (header_ 0).val≠0 → (header_ 1).val=input.placement.cap →
    (header_ 2).val=(localRank (Z).graph res (GroupStage.depthBound D n f g) (shapeAt side t q₀)).val →
    freshAt (Config.relabel shape B.dimension.symm raw) side t q₀ :=by
  subst batch
  intro row header_ captured active capacity shapeWord
  exact ⟨active,capacity,captured,shapeWord⟩

local notation "candidate" => (v).receiver
local notation:max "rowsAt" dd:arg ready:arg mem:arg cd:arg μ:arg measured:arg dst:arg =>
  DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    dd ready mem cd μ measured dst
local notation:max "observed" ready:arg dst:arg block:arg size:arg shape:arg rh:arg rg:arg law:arg =>
  DateInputs.ObservedFreshRow (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue
    io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom ready dst
    block size shape rh rg law

include accepted in
set_option maxHeartbeats 1800000 in
theorem DateInputs.fall_observation_at_slot
    (dd:venue.degree=D) (ready:(u).Ready) (mem:Memory w) (cd:input.placement.cap=cap)
    (gr:z=S.grainAt G.b p (age+1)) (μ:DescentGL.Layout (E).dim) (measured dst:Memory w)
    (atDate:rowsAt dd ready mem cd μ measured dst) (elapsed:0<age) (sorted:SourceSorted W input.order)
    (block:Fin (candidate).blocks) (size:HH*rows=(C₀).placement.sparse) (shape:config=K₁)
    (hx:(candidate).blocks=2^k) (aligned:(candidate).hosts=(v).sheets.hosts)
    (groupsAt:(candidate).groups=group₁) (rh:Fin (candidate).hosts) (rg:Fin (candidate).groups)
    (side:Bool) (t:(Z).Fallback) (q₀:DescentContactTree.Physical.Site ((Z).placement.fallbackBook side t).height)
    (found:operandLocation B (block.cast hx) (rh.cast aligned) (rg.cast groupsAt)=some (place side t q₀)) :
    observed ready dst block size shape rh rg (fun row=>freshAt row side t q₀) :=by
  apply location_pullback B hx aligned groupsAt
    (fun x h₁ g₁=>observed ready dst x size shape h₁ g₁ (fun row=>freshAt row side t q₀))
    block rh rg (place side t q₀) found
  obtain ⟨hRaw,sRaw,xCount,menu,digits₀,read,hdr,xs,root,row,activeRead,capacity,shapeWord⟩:=
    DateInputs.fromNamed_fallback_rows (B:=B) accepted drift degree payload e previous M nextM oldLanes
      primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
      previousArguments initial prepared sceneRoom dd ready mem cd gr μ measured dst atDate elapsed sorted side t q₀
  refine ⟨menu,read,?_⟩
  let where_:=place side t q₀
  let raw:=(u).menu.publicData sh start count io.hubs g (2^n) (stage_ where_.2) (regs_ where_.2)
    menu digits₀ where_.2.val (((denseOrder B) where_.1.2).castLE B.next.valid.host) where_.1.1
  exact fallback_at_batch (B:=B) (drift:=drift) (degree:=degree) (payload:=payload) (e:=e) (previous:=previous)
    (M:=M) (nextM:=nextM) (oldLanes:=oldLanes) (primitiveLanes:=primitiveLanes) (printedBits:=printedBits)
    (venue:=venue) (io:=io) (floor:=floor) (w:=w) (fitsStencil:=fitsStencil) (fitsSigned:=fitsSigned)
    (fitsCut:=fitsCut) (count:=count) (previousMeta:=previousMeta) (previousArguments:=previousArguments)
    (initial:=initial) (prepared:=prepared) (sceneRoom:=sceneRoom) stages₁ (funded_units B accepted gr).symm
    (cfgEq dd cd gr) shape raw side t q₀ row activeRead capacity shapeWord

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
