import OAI.Hierarchy.DescentNamedFundedPacket
import OAI.Hierarchy.DescentNamedEarlierPlacement
import OAI.Hierarchy.DescentNamedPackedOperandPointers

namespace OAI
/-! # Both original packed public inputs at the authentic saved root image -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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
  (venue : StageVenueTail.Date)
  (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
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
variable (run : (DateInputs.fromNamed G S ctl.board k tail age p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom).FinalInputs) (measured : Memory w)
local notation "r₀" => (Z).k-(T).commonDepth
local notation "dep₀" => GroupStage.depthBound D n f g
local notation "src₀" => (im).receiver.preparedMid (im).book (im).prepared measured
local notation "rrank" => fun v j=>(ranks («a»:=r₀) (Y:=2^(Z).n) (D:=input.placement.degree)
  ((im).book.common (im).receiver.projectionEnd HH) (2^dep₀) (dep₀+2) src₀ v j).val
local notation "fees" => fundedPorts (funded_residual B) B.dimension run.ports
local notation "saved_" hdr:arg xs:arg => root_snapshot B input.valid.host (im).receiver (im).book (im).prepared measured hdr xs


local notation "O" => (v).setup.packets
local notation "hold" => (rc).preparedImage (u).book (u).bookFits measured
local notation "packetBits" f₀:arg => (O).oldBits*((O).stage 0 f₀).fields

/-- Real resident data for the two subsequent chronological packet gathers.
Widths are the two original record arities and the old root lane pitch. -/
def DateInputs.OriginalPackedInputs : Prop :=
  ∃words : (f₀:Bool)→Fin (O).actors→Fin ((O).groups*(O).blocks)→Cell (packetBits f₀),
    ∀f₀,Source ((O).original f₀) (words f₀) (O).beforeLanes hold

private theorem packed_source_cast {originalBits b H H' J J' lanes bw : ℕ}
    (width : b=originalBits) (hosts : H'=H) (groups : J'=J) (operand : Expr)
    (values : Fin H→Fin J→Cell originalBits) (mem : Memory bw) (read : Source operand values lanes mem) :
    ∃out : Fin H'→Fin J'→Cell b, Source operand out lanes mem ∧
      ∀r j,(out r j).val=(values (r.cast hosts) (j.cast groups)).val := by
  subst_vars
  exact ⟨values,read,fun _ _=>rfl⟩

local notation "afterGroups" => (O).groups*(O).blocks
local notation "span_" => (Z).k-(T).commonDepth
local notation "field_" => (u).roots.field
local notation "goods_" => (v).setup
variable (hdr : OriginalHeader B input.valid.host (im).receiver (im).book measured)
    (xs : OriginalArrays B input.valid.host field_)
    (packetRead : ClosedReset.Window.RootPacket B (im).receiver (im).book (im).prepared measured
      hdr (im).sources xs nBits tBits)
    (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (low : dep₀+2<w)
    (capacity : venue.cap=cap) (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
local notation "cargo_" => calendar_sender_matrix B (2^e) field_ (im).receiver (im).book (im).prepared measured hdr xs
local notation "wire_" => DescentRotorWindowArchive.count input.placement.degree (2^span_) input.placement.cap

include run packetRead ready chosen pitch small word ceiling low capacity gr fee in
/-- Both original records retain their natural values when transported from the old
root coordinates to the packet gatherer's physical host and group types. -/
theorem DateInputs.fromNamed_public_packed_values :
    ∃(groupAt : afterGroups=2^(T).commonDepth)
      (words : (side : Bool)→Fin (O).actors→Fin afterGroups→Cell (packetBits side)),
      (∀side,Source ((O).original side) (words side) (O).beforeLanes hold) ∧
      (∀r j,(words false r j).val=(savedInput B input.valid.host (saved_ hdr xs) r (j.cast groupAt)).val) ∧
      ∀r j,(words true r j).val=(encode field_ wire_ (cargo_ r (j.cast groupAt))).val := by
  have fallback:=DateInputs.fromNamed_saved_fallback (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom degreeAt capAt run measured hdr xs packetRead ready chosen pitch small word ceiling low
  obtain ⟨matrix,_,matrixRead,_,atMatrix,_⟩:=DateInputs.fromNamed_earlier_placement (B:=B) drift degree payload
    e previous M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling
    capacity gr fee measured hdr xs packetRead
  have priorAddress := (DateInputs.named_packet_registers G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom run ctl.base ctl.radix B.age).1
  rw [←priorAddress] at matrixRead
  have grouped : afterGroups=2^(T).commonDepth:=by
    rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix]
    rfl
  have oldGroups : (goods_).retained.grouped=2^(T).commonDepth:=by rw [B.commonDepth];rfl
  have currentDegree:=degreeAt.trans input.branch.symm
  have fallbackWidth : packetBits false=field_*DescentFallbackPeriod.inputCount input.placement.degree
      (2^span_) input.placement.cap (Z).n span_ := by
    change field_*DescentFallbackPeriod.inputCount venue.degree (2^k) cap n k=_
    rw [currentDegree,calendar_residual B,capAt,B.dimension]
  have windowWidth : packetBits true=(goods_).seven.control.rootWidth:=by
    change field_*DescentRotorWindowArchive.count venue.degree (2^k) cap=
      field_*DescentRotorWindowArchive.count venue.degree (goods_).retained.donors cap
    rw [(u).menu.donors]
    rfl
  obtain ⟨fRead,lowBank,fVal⟩:=packed_source_cast fallbackWidth rfl grouped _ _ _ fallback
  obtain ⟨mRead,hiBank,mVal⟩:=packed_source_cast windowWidth rfl (grouped.trans oldGroups.symm) _ _ _ matrixRead
  let received : (side : Bool)→Fin (O).actors→Fin afterGroups→Cell (packetBits side)
    | false => fRead
    | true => mRead
  refine ⟨grouped,received,?_,fVal,?_⟩
  · intro side; cases side
    · exact lowBank
    · exact hiBank
  · intro r j
    exact (mVal r j).trans (atMatrix _ _)

include run hdr xs packetRead ready chosen pitch small word ceiling low capacity gr fee in
theorem DateInputs.fromNamed_public_packed_inputs :
    ∃words : (side:Bool)→Fin (O).actors→Fin afterGroups→Cell (packetBits side),
      ∀side,Source ((O).original side) (words side) (O).beforeLanes hold := by
  obtain ⟨_,words,reads,_,_⟩:=DateInputs.fromNamed_public_packed_values (B:=B) drift degree payload e previous
    M nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom degreeAt capAt run measured hdr xs packetRead ready
    chosen pitch small word ceiling low capacity gr fee
  exact ⟨words,reads⟩


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
