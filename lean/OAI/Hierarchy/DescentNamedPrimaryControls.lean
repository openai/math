import OAI.Hierarchy.DescentNamedIncomingOperandRead
import OAI.Hierarchy.DescentNamedRetainedFeeVolume

namespace OAI
/-! # Original terminal and grain values on both physical correction sources -/
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
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
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
variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "inputAt" pr:arg sc:arg => I₀ previousMeta previousArguments initial pr sc
set_option hygiene false
local notation "u" => inputAt prepared sceneRoom

open DescentResetLocalRoster DescentSixParty.ClosedReset.Window

open DescentResetSourceTicketCompare DescentResetTrunkCompactPointer DescentResetFieldAssembler
open scoped BigOperators

local notation "A₁" => (v).receiver
local notation "F₀" => (v).front
local notation "C₀" => (v).setup
local notation "H₀" => S.hostSize age
local notation "H₁" => S.hostSize (age+1)
local notation "G₁" => S.groupCount (age+1)
local notation "keyWidth" => originalBits D k n (GroupStage.depthBound D n f g)
  input.placement.cap (programCount board (GroupStage.depthBound D n f g)) g
local notation "rank₀" => B.frame.host.symm.toEmbedding.trans (input.vertex.trans (Fin.castLEEmb input.valid.host))
local notation "dense₀" => (B.reset.denseHostRank B.terminals rank₀).trans (Fin.castLEEmb B.next.valid.host)
local notation "rack₀" => rackOf B dense₀
local notation "st" => (v).sheetsStart base₀
local notation "FEE" x:arg j:arg h:arg gr:arg => ∑l,feeAt (wordBefore B) (original_fees (b:=keyWidth) B rack₀ x h gr) j l
local notation "first₀" => (v).operandFloor base₀
local notation "dst" ok:arg m:arg => ((C₀).code first₀ w (u).bank (u).laws).image ((u).beforeSetupImage ok m)

local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "primary" t:arg => (blocks B).src (trunkParent B t)

set_option hygiene true

set_option maxHeartbeats 1000000 in
/-- Both physical input expressions and their values on every old terminal and
its incoming grains in the same selected date. -/
theorem DateInputs.fromNamed_primary_controls
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (paid : input.placement.cap=cap)
    (ok : (u).Ready) (m : Memory w)
    (earned : ActorTrunkReads B input.valid.host (F₀) ((v).actorEnd base₀)
      ((v).issuedScene base₀ (u).earlier) (u).sceneFits m)
    (src : RankSources B (b:=(v).sheets.metaBits) (t:=keyWidth) (M:=(v).sheets.lanes) rack₀
      ((v).rankPorts base₀) (sheetHeader B st (u).sectors.pageBits) (sheetOriginal B st (u).sectors.pageBits)
      (((v).rankPortPhase base₀ w).image ((u).before_ports ok m)))
    :
    ∃(hub : Fin H₁→Fin G₁→Cell (C₀).fieldBits)
     (fee : Fin (2^k)→Fin (C₀).strip→Fin H₁→Fin G₁→Cell (C₀).fieldBits),
      (∀t,hub (dense₀ (primary t).1.2) (primary t).1.1=
        if ((B.terminals.code t).2.2.isSome) then 0 else 1) ∧
      (∀(t : B.reset.Fallback) (z₀ : (old).graph.Edge),B.terminals.home ((old).graph.dst z₀)=t→
        ∀j : Fin (C₀).strip,j.val=(incomingIndex B z₀).val→
        (fee (primary t).2 j (dense₀ (primary t).1.2) (primary t).1.1).val=earlierIncoming B z₀) ∧
      (∀x,((v).retainedHub base₀ x).Fits w ((C₀).casts first₀) ∧
        Source ((v).retainedHub base₀ x) hub M (dst ok m)) ∧
      (∀x j,((v).retainedTicket base₀ x j).Fits w ((C₀).casts first₀) ∧
        Source ((v).retainedTicket base₀ x j) (fee x j) M (dst ok m)) ∧
      (∀x j h gr,(fee x j h gr).val≤B.next.placement.cap) :=by
  obtain ⟨sel,hub,fee,positions,hubAt,feeAt_,hubRead,feeRead,feeBound⟩:=
    DateInputs.fromNamed_retained_fee_volume (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt paid ok m earned src
  have width : (v).sheets.metaBits≤(C₀).fieldBits:=by
    change (v).sheets.metaBits≤ max _ (max 1 (max _ (v).sheets.metaBits))
    exact (Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have fieldRoom:=src.small.trans_le (Nat.pow_le_pow_right (by decide : 0<2) width)
  refine ⟨hub,fee,?_,?_,hubRead,feeRead,feeBound⟩
  · exact recorded_primary_hub B input.valid.host B.next.valid.host hub hubAt
  · intro t edge land j atSlot
    exact recorded_incoming_value B rack₀ input.valid.host B.next.valid.host
      src.age src.sorted (rack_present B dense₀) src.units src.nearOld src.codeRoom fieldRoom
      sel positions fee feeAt_ t edge land j atSlot

def DateInputs.PrimaryWordsAt (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ok : (u).Ready) (m : Memory w)
    (hub : Fin H₁→Fin G₁→Cell (C₀).fieldBits)
     (fee : Fin (2^k)→Fin (C₀).strip→Fin H₁→Fin G₁→Cell (C₀).fieldBits) : Prop :=
      (∀t,hub (dense₀ (primary t).1.2) (primary t).1.1=
        if ((B.terminals.code t).2.2.isSome) then 0 else 1) ∧
      (∀(t : B.reset.Fallback) (z₀ : (old).graph.Edge),B.terminals.home ((old).graph.dst z₀)=t→
        ∀j : Fin (C₀).strip,j.val=(incomingIndex B z₀).val→
        (fee (primary t).2 j (dense₀ (primary t).1.2) (primary t).1.1).val=earlierIncoming B z₀) ∧
      (∀x,((v).retainedHub base₀ x).Fits w ((C₀).casts first₀) ∧
        Source ((v).retainedHub base₀ x) hub M (dst ok m)) ∧
      (∀x j,((v).retainedTicket base₀ x j).Fits w ((C₀).casts first₀) ∧
        Source ((v).retainedTicket base₀ x j) (fee x j) M (dst ok m)) ∧
      (∀x j h gr,(fee x j h gr).val≤B.next.placement.cap)

def DateInputs.PrimaryControlsAt (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ok : (u).Ready) (m : Memory w) : Prop :=
    ∃(hub : Fin H₁→Fin G₁→Cell (C₀).fieldBits)
     (fee : Fin (2^k)→Fin (C₀).strip→Fin H₁→Fin G₁→Cell (C₀).fieldBits),
      DateInputs.PrimaryWordsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
        printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
        initial prepared sceneRoom ok m hub fee


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
