import OAI.Hierarchy.DescentNamedRegisterBook
import OAI.Hierarchy.DescentNamedCalendarRootPacket

namespace OAI
/-! # Chronological fresh gate registers from the actually measured reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
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
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
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
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentFallbackPeriod.Projected DescentPaidResidentCount.Reset
local notation "sources" => atlasSender atlas sh start count io.hubs g (2^n) roots w
local notation "middle" => (v).middle
local notation "X₀" => Receiver.IndexedRoots.mk (rc) (book) prepared (sources)
local notation "fac" => 32*Nat.clog 2 (2*venue.degree)
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "pg" => ((false,.inr (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le k) (by decide)⟩,none)) : DescentSixParty.Chronology.RootPage k (2^n))
local notation "deckNow" => Receiver.IssuedDeck.mk (atlas).directions (atlas).board (atlas).primitive pg
local notation "menu" => (deckNow).reindex (degreeAt.trans input.branch.symm) B.dimension.symm (ClosedReset.Window.calendar_residual B).symm



open DescentKernelHistory DescentLocalArchiveOrder DescentSixParty.Chronology Reached.NodeCells DescentStageEdgeReceipt
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "field" => (v).middle.rootField
local notation "stRun" => (a).throughStencil (u).shape start (u).count (u).hub (u).g (u).Y (u).src (u).sourceRows (u).oldDegree w
local notation "stTime" => (a).throughStencilTicks (u).shape start (u).count (u).hub (u).g (u).Y (u).sourceRows (u).oldDegree w

private theorem root_units_fit (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
    oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload) :
    ∀j∈(v).rootUnits,j*(v).receiver.lanes≤payload/2 := by
  subst M
  subst e
  obtain ⟨rootsEq, receiversEq, _, _⟩ := selected_inventory G S board k tail age p f g drift degree payload
    previous nextM C packet oldLanes primitiveLanes printedBits venue io.wire io.roster floor
  unfold selected at rootsEq receiversEq
  unfold ResetOutput.groupWidth at small
  rw [rootsEq, receiversEq] at small
  intro j hj
  exact selected_room G S board k tail age p f g drift degree payload previous nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor j small (Or.inl hj)

include accepted in
/-- The original signed/stencil packet, its attained reserve and the two actual executions
give the complete fresh-register source at the chronological final class state. -/
def FinalInputs.fromNamed_original_register (z₀ : (u).FinalInputs) (safe : z₀.Room)
    [Fintype X] (whole : p∣B.reset.unit) (history : Archive W)
    (earlier : Local history.bit)
(ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (measured : Memory w) (μ : DescentGL.Layout (E).dim)
    (reservation : ClosedReset.Recorded.StencilReservationWords (reset:=B) E
      ((sh).dimension.symm.trans B.keyWidth.symm) venue.degree degreeAt.symm.le measured)
    (order : (P).S.OldOrder (P).X (P).base (P).bank g (T).commonDepth μ measured)
    (panel : ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
      count (E).depthRows (rc).stencil book measured) (popFit : count.Fits w floor)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent) (hosts : HH<2^w)
    (branch : G.b≤2^S.capGain) (elapsed : 0<age) (sorted : SourceSorted W input.order)
    (mass : 0<amp) (activeDegree : 0<32*Nat.clog 2 (2*input.placement.degree))
    (hdr : OriginalHeader B input.valid.host (im).receiver (im).book measured)
    (raw : OriginalArrays B input.valid.host field)
    (packetRead : ClosedReset.Window.RootPacket B (im).receiver (im).book (im).prepared measured hdr (im).sources raw nBits tBits)
    {before result : Memory w} (measuredAt : (stRun).Exec before measured stTime)
    (spent : (u).throughOperandDate.Runs before result) :
    DescentPrimitivePalette.RootRegister B accepted.positive whole history earlier (v).birth z₀.guards
      (z₀.classImage result) rfl rfl rfl:=by
  obtain ⟨books,rows⟩:=fromNamed_root_register_kit (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt gr fee
  have operands:=fromNamed_root_area (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    degreeAt capAt ready chosen pitch small word ceiling
  have control:=DateInputs.root_packet_controls (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
    prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling score measured μ reservation order panel
    popFit gr fee hosts
  have bought := root_units_fit (ctl:=ctl) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor chosen pitch small
  have short:=fromNamed_guard_room (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil count degreeAt capAt pitch bought word
  have bounds:=chosen_root_pages_fit G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch small word ceiling
  have top:=fromNamed_register_end (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
  have atEnd:=FinalInputs.fromNamed_register_frame (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    degreeAt capAt z₀ ready safe measuredAt spent
  have groups:=fromNamed_register_groups (B:=B)
  have bill : ClosedReset.calendarBatchCount S n ctl.bitsR f input.placement.cap G.b (age+1)=(atlas).batches:=by
    exact fromNamed_stop (capAt:=capAt) (fitsStencil:=fitsStencil) ..
  obtain ⟨baseRoom,dimRoom,levelRoom,capRoom,narrow,level,one,amount,shape,quotaPos⟩:=
    fromNamed_original_limits (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor capAt gr fee branch
  let namedBoard := B.rootRegisterLayout (v).birth
  let issuedBoard := { namedBoard with
    rootBits := (atlas).instructionBits
    stop := (atlas).batches
    sourceLanes := (v).middle.signedLanes }
  have fresh : DescentPrimitivePalette.RootRegister B accepted.positive whole history earlier issuedBoard
      (DescentPrimitiveBirth.guards ((im).receiver.headerEnd (im).book) HH (S.groupCount (age+1)*2^k) (2^e)
        ((Z).k-(T).commonDepth) (Z).n input.placement.degree) (z₀.classImage result) rfl rfl rfl:=
    DescentPrimitivePalette.issued_root_register
    (nodes:=(v).birth.nodes) (args:=(v).birth.arguments) (lanes:=(v).birth.placement.lanes)
    (classes:=(v).birth.classBits) (priceBits:=(v).birth.paidBits) (spanBits:=(v).birth.spanBits) B accepted.positive whole history earlier accepted groups
    (im).receiver (im).book (im).prepared measured hdr (im).sources raw packetRead
    E (P).S (P).X (P).base (P).bank g (menu).peers (atlas).hostIndex (.lit input.placement.cap)
    (quota S.rounds) amp (P).S.total (a).ports (atlas).factor (menu).page rfl books rows operands control
    short (Nat.two_pow_pos _) ((im).receiver.preparedEnd (im).book) (z₀.classImage result) le_rfl
    (by rw [top];exact bounds.1) atEnd elapsed sorted baseRoom dimRoom levelRoom capRoom narrow level one amount shape
    mass quotaPos activeDegree (age+1) gr bill.le
  have rootStop : (atlas).batches = (v).birth.stop := by
    change DescentRecordedRotorLayers.layers n packet f ((2*cap)/2) * ResetInput.calendarLanes S G.b (age+1) =
      DescentRecordedRotorLayers.layers n packet f cap * ResetInput.calendarLanes S G.b (age+1)
    rw [show (2*cap)/2=cap by omega]
  have boardEq : issuedBoard = namedBoard := by
    dsimp only [issuedBoard]
    rw [rootStop]
    rfl
  have layout : namedBoard=(v).birth:=
    ResetOutput.born_layout B p drift degree payload e previous M nextM
      (ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue) base₀ degreeAt
  have state:=fromNamed_root_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt measured
  have attached:=z₀.original_guards ((im).receiver.headerEnd (im).book) HH (S.groupCount (age+1)*2^k) (2^e)
    ((Z).k-(T).commonDepth) (Z).n input.placement.degree state.2.2.2.1 rfl
    (groups.trans (congrArg (2^·) B.commonDepth)) rfl (ClosedReset.Window.calendar_residual B) B.dimension
    (input.branch.trans degreeAt.symm)
  exact DescentPrimitivePalette.RootRegister.onBoard B accepted.positive whole history earlier (boardEq.trans layout) attached fresh

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
