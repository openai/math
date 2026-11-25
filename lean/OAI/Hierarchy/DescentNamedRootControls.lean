import OAI.Hierarchy.DescentNamedRootPacketRooms
import OAI.Hierarchy.DescentIndexedEarlierPlacement

namespace OAI
/-! # The reached old capacity and attained depth on every padded root lane -/
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
open DescentGL DescentGroupPeerOrder DescentFallbackRankRAM
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
local notation "fac" => 32*Nat.clog 2 (2*venue.degree)
local notation "staged" => fromNamed_matrix_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
open DescentPlainTerminal.Suffix DescentPacking.PackedMatch.Local.Stage.Chooser
local notation "head" => (P).S.header (P).base
local notation "field" => (v).middle.rootField
local notation:max "mid" m₀:arg => (im).receiver.preparedMid (im).book (im).prepared m₀
local notation "ceil" => (im).receiver.headerEnd (im).book
local notation "depths" => ClosedReset.Recorded.oldDepth B
local notation "coarse" => (T).commonDepth
local notation "span" => (Z).k-coarse
local notation "cat" => RootTemplates.arena ceil HH (2^coarse) (2^e) span (Z).n input.placement.degree
local notation "pop" => Fintype.card input.V

theorem DateInputs.root_packet_controls (ready : (u).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(v).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (measured : Memory w) (μ : DescentGL.Layout (E).dim)
    (reservation : ClosedReset.Recorded.StencilReservationWords (reset:=B) E
      ((sh).dimension.symm.trans B.keyWidth.symm) venue.degree degreeAt.symm.le measured)
    (order : (P).S.OldOrder (P).X (P).base (P).bank g coarse μ measured)
    (panel : ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
      count (E).depthRows (rc).stencil book measured) (popFit : count.Fits w floor)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent) (hosts : HH<2^w) :
    Source (im).sources.priorCap (fun (_ : Fin HH) (_ : DescentColonies.Block coarse)=>(input.placement.cap : Cell field))
      (2^e) (mid measured) ∧
    Source (im).sources.relativeDepth (fun (v₀ : Fin HH) (_ : DescentColonies.Block coarse)=>
      (Receiver.depthDigit coarse pop depths v₀ : Cell field)) (2^e) (mid measured) :=by
  obtain ⟨chart,addr,priorDepths,range,stored,common,short,counted,owner,_,_⟩:=
    DateInputs.named_root_packet_rooms (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling score measured μ reservation order panel popFit
  obtain ⟨books,rows⟩:=fromNamed_root_image_calendar (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt gr fee
  have bits : Nat.clog 2 (cap+1)≤field:=by
    change Nat.clog 2 (cap+1) ≤ ResetMiddle.fieldWidth venue.degree cap n k Ht
    exact (le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have room : input.placement.cap<2^field:=by
    rw [capAt]
    exact (Nat.lt_succ_self cap).trans_le ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) bits))
  exact ClosedReset.Window.indexed_root_controls B (2^e) field (im) E (P).S (P).X (P).base (P).bank
    g _ (atlas).hostIndex (quota S.rounds) (P).S.total (a).ports (atlas).groupDigits (atlas).batches
    (atlas).factor _ _ measured books rows pop depths rfl hosts input.valid.host chart addr priorDepths range
    stored common short counted owner room

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
