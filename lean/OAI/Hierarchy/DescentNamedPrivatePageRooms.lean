import OAI.Hierarchy.DescentNamedOriginalHeader
import OAI.Hierarchy.DescentAtlasPacketAddresses
import OAI.Hierarchy.DescentResetPeerRootPages

namespace OAI
/-! # Earlier exceptional root-bank apertures on the attained named reset -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver

namespace IndexedRoots
variable {D cap N n r c H G K R M hm lb tiny field Ht w : ℕ}
  {D' cap' n' r' c' H' G' Ht' : ℕ}
variable (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
  (degree : D=D') (capacity : cap=cap') (dimension : n=n') (residual : r=r')
  (depth : c=c') (hosts : H=H') (groups : G=G') (height : Ht=Ht')


open DescentPackedColony DescentSIMDLookup DescentResetHostSize ProtocolRAM
open DescentSixParty.Chronology DescentSixParty
noncomputable section

def PageRooms : Prop :=
  let arena:=RootTemplates.arena (x.receiver.headerEnd x.book) H (2^c) M r n D
  ∀ p : RootPage r (2^n),
    (∀j,((x.book.table p).2.reads j).Fits w (arena.middle (rootIndex r (2^n) p).val)) ∧
    M*max ((x.book.table p).2.field*(x.book.table p).1) (x.book.table p).2.outputBits≤w/2

theorem reindex_page_rooms (prior : x.PageRooms) :
    (x.reindex degree capacity dimension residual depth hosts groups height).PageRooms:=by
  subst D';subst cap';subst n';subst r';subst c';subst H';subst G';subst Ht';exact prior

end
end IndexedRoots
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentSixParty.Chronology
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
local notation "cap" => (cal.take age).prod*256
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

theorem DateInputs.fromNamed_all_page_rooms (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) : (im).PageRooms:=by
  have limits:=chosen_root_pages_fit G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch small word ceiling
  have rows:=(atlas_packet_addresses atlas sh start count io.hubs g (2^n) roots ready.stencil ready.prime.fit
    prepared.toPrefixFits limits.1 rfl rfl rfl rfl rfl limits.2).2.2.2.2
  have original : (X₀).PageRooms:=fun page=>⟨rows page,limits.2 page⟩
  exact (X₀).reindex_page_rooms _ _ _ _ _ _ _ _ original

theorem DateInputs.fromNamed_private_page_rooms (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) :
    (∀s root j,let pg : RootPage ((Z).k-(T).commonDepth) (2^(Z).n):=Receiver.privatePage s root
      ;(((im).book.table pg).2.reads j).Fits w ((RootTemplates.arena ((im).receiver.headerEnd (im).book)
        HH (2^(T).commonDepth) (2^e) ((Z).k-(T).commonDepth) (Z).n input.placement.degree).middle
          (rootIndex ((Z).k-(T).commonDepth) (2^(Z).n) pg).val)) ∧
    ∀s root,let pg : RootPage ((Z).k-(T).commonDepth) (2^(Z).n):=Receiver.privatePage s root
      ;(2^e)*max (((im).book.table pg).2.field*((im).book.table pg).1) ((im).book.table pg).2.outputBits≤w/2:=by
  have result:=DateInputs.fromNamed_all_page_rooms (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling
  exact ⟨fun s root=>(result (Receiver.privatePage s root)).1,fun s root=>(result (Receiver.privatePage s root)).2⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
