import OAI.Hierarchy.DescentNamedPackedOperandPointers
import OAI.Hierarchy.DescentIndexedFundedWords
import OAI.Hierarchy.DescentNamedCalendarRootPacket
import OAI.Hierarchy.DescentPhysicalFundedRoots

namespace OAI
/-! # The original named funded census reads the same packed words as its saved root observation -/
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
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
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
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)

local notation "staged" => fromNamed_matrix_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt

open DescentFundedCensus DescentPaidResidentCount.Reset DescentSixParty.ClosedReset.Window
open DescentSharedBookScan DescentPackedColony
open private Hierarchy.DescentPaidResidentCount.Reset.packet_preserved from OAI.Hierarchy.DescentPhysicalFundedRoots
variable (run : (DateInputs.fromNamed G S ctl.board k tail age p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom).FinalInputs) (measured : Memory w)
local notation "r₀" => (Z).k-(T).commonDepth
local notation "dep₀" => GroupStage.depthBound D n f g
local notation "src₀" => (im).receiver.preparedMid (im).book (im).prepared measured
local notation "rrank" => fun host₀ j=>(ranks («a»:=r₀) (Y:=2^(Z).n) (D:=input.placement.degree)
  ((im).book.common (im).receiver.projectionEnd HH) (2^dep₀) (dep₀+2) src₀ host₀ j).val
local notation "fees" => fundedPorts (funded_residual B) B.dimension run.ports
local notation "saved_" hdr:arg xs:arg => root_snapshot B input.valid.host (im).receiver (im).book (im).prepared measured hdr xs

theorem DateInputs.fromNamed_funded_packet {nbits : ℕ} (hdr : OriginalHeader B input.valid.host (im).receiver (im).book measured)
    (xs : OriginalArrays B input.valid.host (u).roots.field)
    (packetRead : ClosedReset.Window.RootPacket B (im).receiver (im).book (im).prepared measured hdr (im).sources xs nbits tBits)
    (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (low : dep₀+2<w) :
    ∀s root,Source ((fees).bank s root) (savedInput B input.valid.host (saved_ hdr xs)) (2^e)
      ((rc).preparedImage (u).book (u).bookFits measured):=by
  let code : DescentResetHostSize.Code (v).middle.rootDepth :=
    ⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let page : Chronology.RootPage (v).middle.rootDepth (2^(v).middle.rotorBits):=(false,.inr (code,none))
  have limits:=chosen_root_pages_fit G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch small word ceiling
  have fundLegal:=(rc).issued_fallback_words ((a).estimator start) (P).S (P).X (P).base (P).bank g
    (atlas).directions (atlas).hostIndex (.lit ((a).c/2)) (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports
    (atlas).board (atlas).packet (atlas).C (atlas).groupDigits (atlas).batches (atlas).layerBits (atlas).factor (atlas).primitive page prepared
  have actual : (im).FallbackWords:=by apply (X₀).reindex_words; exact fundLegal
  have check:=(atlas_geometry atlas sh start count io.hubs g (2^n) roots ready.stencil ready.prime.fit
    prepared.toPrefixFits limits.1 rfl rfl rfl rfl rfl limits.2).2
  have enough:=(atlas_packet_addresses atlas sh start count io.hubs g (2^n) roots ready.stencil ready.prime.fit
    prepared.toPrefixFits limits.1 rfl rfl rfl rfl rfl limits.2).2.2
  have checked : (im).sources.OperandRoom HH (2^(T).commonDepth) (2^e) w ((im).receiver.headerEnd (im).book):=by
    apply (X₀).reindex_root_room
    exact check
  have spans : (∀i,HH*chunks (2^(T).commonDepth) (2^e)≤((im).sources.here i).size) ∧
      ∀i j,HH*chunks (2^(T).commonDepth) (2^e)≤((im).sources.signed i j).size:=by
    apply (X₀).reindex_span
    exact ⟨fun i=>(enough.1 i).2,fun i j=>(enough.2.1 i j).2⟩
  have pages:=DateInputs.fromNamed_all_page_rooms (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling
  have addr : ∀s t,(fees).bank s t=(im).receiver.gatheredOperand (im).book (s,.inr t):=by
    apply (X₀).reindex_funded_bank
    intro s t;rfl
  have memory : (im).receiver.preparedImage (im).book (im).prepared measured=(rc).preparedImage book prepared measured:=
    ((X₀).unchanged (degreeAt.trans input.branch.symm) ((show (a).c/2=cap by change (2*cap)/2=cap;omega).trans capAt.symm)
      B.dimension.symm (funded_residual B).symm B.commonDepth.symm rfl (S.group_power ctl.base ctl.radix age)
      (congrArg (fun j=>GroupStage.depthBound j n f g) degreeAt) measured).2.2.2.2.2
  have axis : 2^r₀=2^(cc+k-(T).commonDepth):=by rw [B.keyWidth]
  let here:=fun host₀ hi (l:Fin (2^r₀))=>xs.stencil host₀ hi (l.cast axis)
  let signed:=originalCable B xs
  intro s t
  rw [addr]
  change Source _ _ _ ((rc).preparedImage book prepared measured)
  rw [←memory]
  have rd:=actual measured s t here xs.peers signed low hdr.rankBits checked packetRead.mounted
    spans.1 spans.2 packetRead.sites packetRead.tagged (fun i j=>packetRead.signed j i) pages
  have same : savedInput B input.valid.host (saved_ hdr xs)=fun h g=>DescentFallbackPeriod.encodePacket
      (DescentFallbackPeriod.inputs (field:=(u).roots.field) here xs.peers signed rrank h g):=by
    funext h g
    apply Fin.ext
    have fromBank := saved_input_eq B input.valid.host (saved_ hdr xs) h g
    have original := root_snapshot_input B input.valid.host (im).receiver (im).book (im).prepared measured hdr xs h g
    exact fromBank.trans ((congrArg Fin.val original).trans
      (Hierarchy.DescentPaidResidentCount.Reset.packet_preserved axis xs.stencil xs.peers xs.marks rrank h g))
  rw [same]
  exact rd

private theorem default_funded_operand {r n k₁ d₁ : ℕ} (de : r=k₁) (di : n=d₁) (ptr : Ports k₁ d₁) :
    (fundedPorts de di ptr).bank false
      (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩,none)=
    ptr.bank false (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩,none) :=by
  subst k₁ d₁
  rfl

include run in
/-- The public fallback gather reads the genuine measured original packet at its actual root address. -/
theorem DateInputs.fromNamed_saved_fallback {nbits : ℕ} (hdr : OriginalHeader B input.valid.host (im).receiver (im).book measured)
    (xs : OriginalArrays B input.valid.host (u).roots.field)
    (packetRead : ClosedReset.Window.RootPacket B (im).receiver (im).book (im).prepared measured hdr (im).sources xs nbits tBits)
    (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (low : dep₀+2<w) :
    Source ((v).setup.packets.original false) (savedInput B input.valid.host (saved_ hdr xs)) (2^e)
      ((rc).preparedImage (u).book (u).bookFits measured) :=by
  have ptrs:=DateInputs.named_packet_registers G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom run ctl.base ctl.radix B.age
  have bankEq := (default_funded_operand (funded_residual B) B.dimension run.ports).trans ptrs.2.1.symm
  apply (congrArg (fun bank => Source bank (savedInput B input.valid.host (saved_ hdr xs)) (2^e)
    ((rc).preparedImage (u).book (u).bookFits measured)) bankEq).mp
  exact DateInputs.fromNamed_funded_packet (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
    sceneRoom degreeAt capAt run measured hdr xs packetRead ready chosen pitch small word ceiling low false _

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
