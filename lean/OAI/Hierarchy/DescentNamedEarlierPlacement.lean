import OAI.Hierarchy.DescentIndexedEarlierPlacement
import OAI.Hierarchy.DescentNamedCalendarRootPacket
import OAI.Hierarchy.DescentDatedRetainedRootFrame

namespace OAI
/-! # Recovered matrix and signed donor words at the original seven-way mover -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 1500000
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
local notation "successor₀" => (a).successor
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
local notation "actorBase" => (successor₀).middle.stop base₀
local notation "early" => (successor₀).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (successor₀).front.SceneRoom early ((successor₀).issuedScene base₀ older) w)
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
local notation "middle" => (successor₀).middle
open DescentGL DescentGroupPeerOrder DescentFallbackRankRAM
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
local notation "fac" => 32*Nat.clog 2 (2*venue.degree)
local notation "staged" => fromNamed_matrix_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
open DescentPlainTerminal.Suffix DescentPacking.PackedMatch.Local.Stage.Chooser
local notation "head" => (P).S.header (P).base
local notation "field" => (successor₀).middle.rootField
local notation "mid" m₀ => (im).receiver.preparedMid (im).book (im).prepared m₀
local notation "ceil" => (im).receiver.headerEnd (im).book
local notation "depths" => ClosedReset.Recorded.oldDepth B
local notation "coarse" => (T).commonDepth
local notation "span" => (Z).k-coarse
local notation "cat" => RootTemplates.arena ceil HH (2^coarse) (2^e) span (Z).n input.placement.degree
local notation "pop" => Fintype.card input.V


open DescentSixParty.ClosedReset.Window
open DescentOperandRootPull
local notation "A₁" => input.placement
local notation "C₁" => (successor₀).setup
local notation "M₁" => 2^e
local notation "done₁" m₀:arg => (rc).preparedImage book prepared m₀
local notation "cargo" X₁:arg m₀:arg hdr₁:arg => calendar_sender_matrix B M₁ field (im).receiver (im).book (im).prepared m₀ hdr₁ X₁
local notation "slot₁" => 2*(A₁).cap
local notation "dgr₁" => degreeAt.trans input.branch.symm
local notation "half₁" => (show (a).c/2=cap by change (2*cap)/2=cap;omega)
local notation "cw₁" => (half₁).trans capAt.symm
local notation "rn₁" => (calendar_residual B).symm
local notation "book₀" => Receiver.IndexedRoots.mk (rc) (book) prepared (sources)

private theorem source_transport {ww count₀ hosts₀ groups₀ bits₀ : ℕ}
    {src₀ dst₀ : Expr} {oldMem newMem : Memory ww} {values₀ : Fin hosts₀→Fin groups₀→Cell bits₀}
    (addrEq : src₀=dst₀) (memEq : oldMem=newMem) (read₀ : Source src₀ values₀ count₀ oldMem) :
    Source dst₀ values₀ count₀ newMem := by
  cases addrEq
  cases memEq
  exact read₀

private theorem source_reindex {b b' H H' J J' M w : ℕ} (bh : b=b') (hh : H=H') (jh : J=J')
    (src : Expr) (x : Fin H'→Fin J'→Cell b') (mem : Memory w) (seen : Source src x M mem) :
    Source src (fun (v : Fin H) (j : Fin J)=> (x (v.cast hh) (j.cast jh)).cast (congrArg (2^·) bh.symm)) M mem :=by
  subst_vars
  exact seen

/-- Both input families of the seven-way mover are read from the actual named root image. -/
theorem DateInputs.fromNamed_earlier_placement (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(successor₀).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (capacity : venue.cap=cap)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (measured : Memory w) (hdr : OriginalHeader B input.valid.host (im).receiver (im).book measured)
    (x : OriginalArrays B input.valid.host field)
    (issued : RootPacket B (im).receiver (im).book (im).prepared measured hdr (im).sources x nBits tBits) :
    let donor:=((u).menu.donors.trans (congrArg (2^·) rn₁))
    let bound:=((u).menu.capacity.trans cw₁)
    let which : Fin (C₁).strip→Fin (C₁).retained.donors×Fin (2*(C₁).oldCap):=finProdFinEquiv.symm
    ∃(X : (C₁).seven.Packets)
      (sig : Fin (C₁).strip→Fin (C₁).placement.oldHosts→Fin ((C₁).placement.groups*(C₁).placement.blocks)→Cell (C₁).signedBits),
      Source (u).bank.window X (C₁).seven.packetLanes (done₁ measured) ∧
      (∀j,Source ((u).bank.signed j) (sig j) (C₁).signedLanes (done₁ measured)) ∧
      (∀v hi, (X v hi).val=(encode field (DescentRotorWindowArchive.count (A₁).degree (2^span) (A₁).cap)
        ((cargo x measured hdr) v ⟨hi.val,by rw [B.commonDepth];exact hi.isLt⟩)).val) ∧
      ∀j v hi, (sig j v hi).val =
        (((DescentSignedCableCodec.encode (originalCable B x v
          ⟨hi.val,by rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix];exact hi.isLt⟩
          ((which j).1.cast donor) ((which j).2.cast (congrArg (2*·) bound)))).val:Cell field)).val :=by
  dsimp only
  have price:=fromNamed_matrix_packing G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch small word ceiling capacity
  have calibrated : M₁ * max (field*DescentRotorWindowArchive.count (A₁).degree (2^span) (A₁).cap)
      (DescentRotorWindowArchive.output (Z).n (2^span) (A₁).cap)≤w/2 :=by
    simpa only [← dgr₁,calendar_residual B,B.dimension,capAt,capacity] using price.1
  have geometry:=fromNamed_root_area (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
    prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling
  obtain ⟨books,tables⟩:=fromNamed_root_image_calendar (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt gr fee
  obtain ⟨rootWord,signedWord⟩:=indexed_earlier_placement B M₁ field (im) E (P).S (P).X (P).base (P).bank
    g _ (atlas).hostIndex (quota S.rounds) (P).S.total (a).ports (atlas).groupDigits (atlas).batches (atlas).factor
    _ _ measured hdr x books tables issued geometry calibrated
  have banks:=(book₀).placement_banks dgr₁ cw₁ B.dimension.symm rn₁ B.commonDepth.symm rfl
    (S.group_power ctl.base ctl.radix age) (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt)
  have state:=fromNamed_root_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt measured
  have endMem := state.2.2.2.2.2
  have namedPacket : (im).receiver.gatheredOperand (im).book (matrixPage span (Z).n)=(u).bank.window:=banks.1
  have rootRead := source_transport namedPacket endMem rootWord
  have group0 : (C₁).retained.grouped=2^coarse:=by rw [B.commonDepth];rfl
  have group1 : (C₁).placement.groups*(C₁).placement.blocks=2^coarse:=by
    rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix];rfl
  have width : (C₁).seven.control.rootWidth=field*DescentRotorWindowArchive.count (A₁).degree (2^span) (A₁).cap:=by
    change field*DescentRotorWindowArchive.count venue.degree (C₁).retained.donors cap=_
    rw [(u).menu.donors,dgr₁,calendar_residual B,capAt]
    rfl
  let signal (j:Fin (C₁).strip) :=
    let xy:Fin (C₁).retained.donors×Fin (2*(C₁).oldCap):=finProdFinEquiv.symm j
    fun v hi=>((DescentSignedCableCodec.encode (originalCable B x v (Fin.cast group1 hi)
      (xy.1.cast ((u).menu.donors.trans (congrArg (2^·) rn₁)))
      (xy.2.cast (congrArg (2*·) ((u).menu.capacity.trans cw₁))))).val:Cell field)
  refine ⟨_,signal,source_reindex width rfl group0 _ _ _ rootRead,?_,fun _ _=>rfl,fun _ _ _=>rfl⟩
  intro j
  let xy:Fin (C₁).retained.donors×Fin (2*(C₁).oldCap):=finProdFinEquiv.symm j
  let lo:=xy.1.cast (u).menu.donors
  let slot:=xy.2.cast (congrArg (2*·) (u).menu.capacity)
  have port:=banks.2 lo slot
  have row := signedWord (slot.cast (congrArg (2*·) cw₁)) (lo.cast (congrArg (2^·) rn₁))
  have currentPort : Expr.lookup ((book₀).sources.signed lo slot) .row = (u).bank.signed j := rfl
  have addrEq := (congrArg (fun b₀=>Expr.lookup b₀ .row) port).trans currentPort
  have signedRead := source_transport addrEq endMem row
  have shifted := source_reindex (show field = field from rfl) (show HH = HH from rfl) group1
    ((u).bank.signed j) _ (done₁ measured) signedRead
  exact shifted

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
