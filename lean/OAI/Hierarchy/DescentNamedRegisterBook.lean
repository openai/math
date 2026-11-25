import OAI.Hierarchy.DescentNamedRootRegisterLayout
import OAI.Hierarchy.DescentNamedOriginalHeader
import OAI.Hierarchy.DescentIssuedRootRegisterKit
import OAI.Hierarchy.DescentFundedJobCalendar
import OAI.Hierarchy.DescentNamedCensusPacketLimits

namespace OAI
/-! # The literal fresh gate dictionary and batch count of the named reset -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver.IssuedDeck
open DescentPackedResetRotorRoles DescentSIMDLookup
open scoped Fin.CommRing
theorem primitive_read {D n r d b D' n' r' : ℕ} (book : IssuedDeck D n r d b)
    (ed:D=D') (en:n=n') (er:r=r') (read:∀t,(book.primitive t).val=role t) :
    (book.reindex ed en er).primitive=(fun t=>(role t:Cell b)):=by
  subst D';subst n';subst r'
  funext t
  apply Fin.ext
  change (book.primitive t).val=role t%2^b
  rw [←read,Nat.mod_eq_of_lt (book.primitive t).isLt]
end Hierarchy.DescentFallbackPeriod.Projected.Receiver.IssuedDeck

namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots
variable {D cap N n r c H G K R M hm lb tiny field Ht w Db cb nb rb depth hosts groups height : ℕ}
theorem end_reindex (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
    (d:D=Db) (cp:cap=cb) (nn:n=nb) (rr:r=rb) (cc:c=depth) (hs:H=hosts) (gg:G=groups) (ht:Ht=height) :
    let y:=x.reindex d cp nn rr cc hs gg ht
    y.receiver.preparedEnd y.book=x.receiver.preparedEnd x.book:=by
  cases d;cases cp;cases nn;cases rr;cases cc;cases hs;cases gg;cases ht
  rfl
end Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 900000
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
include accepted in
/-- Both members reconstruct the issued native root book at the reached coordinate system. -/
theorem fromNamed_root_register_kit (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent) :
    (im).book=(im).receiver.issuedBook E (P).S (P).X (P).base (P).bank g (menu).peers (atlas).hostIndex
      (.lit input.placement.cap) f (quota S.rounds) (input.placement.wire*(input.placement.z*G.b)*input.placement.cap) (P).S.total (a).ports (Z).graph (Z).width
      C ((Z).unit/p) (atlas).batches (DescentRecordedRotorLayers.width f input.placement.cap) (atlas).factor (fun tag=>(DescentPackedResetRotorRoles.role tag:DescentSIMDLookup.Cell (atlas).instructionBits)) (menu).page ∧
    (im).sources=(im).receiver.atlasSources E (P).S (P).X (P).base (P).bank g (menu).peers (atlas).hostIndex
      (.lit input.placement.cap) f (quota S.rounds) (input.placement.wire*(input.placement.z*G.b)*input.placement.cap) (P).S.total (a).ports (Z).graph (Z).width
      C ((Z).unit/p) (atlas).batches (DescentRecordedRotorLayers.width f input.placement.cap) (atlas).factor (fun tag=>(DescentPackedResetRotorRoles.role tag:DescentSIMDLookup.Cell (atlas).instructionBits)) (menu).page :=by

  have code:=(deckNow).primitive_read (degreeAt.trans input.branch.symm) B.dimension.symm
    (ClosedReset.Window.calendar_residual B).symm (fun _=>rfl)
  have stride : (atlas).groupDigits=(Z).unit/p := (ClosedReset.Window.funded_units B accepted gr).symm
  simpa only [stride,code] using fromNamed_root_image_calendar (B:=B) drift degree payload e previous M
    nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt gr fee

include capAt in
theorem fromNamed_stop :
    ClosedReset.calendarBatchCount S n ctl.bitsR f input.placement.cap G.b (age+1)=(atlas).batches:=by
  rw [capAt]
  change DescentRecordedRotorLayers.layers n packet f cap * ResetInput.calendarLanes S G.b (age+1) =
    DescentRecordedRotorLayers.layers n packet f ((2*cap)/2) * ResetInput.calendarLanes S G.b (age+1)
  rw [show (2*cap)/2=cap by omega]


include degreeAt capAt in
/-- Each actual guarded opcode fits the two already-installed root lookups. -/
theorem fromNamed_guard_room (pitch : M=2^e)
    (selected : ∀t∈(v).rootUnits,t*(v).receiver.lanes≤payload/2) (machine : payload≤w) :
    2^e*max ((v).middle.rootField*DescentIssuedRotorRoles.guardInputs input.placement.degree
      (2^((Z).k-B.terminals.commonDepth)) input.placement.cap) ((atlas).instructionBits*(atlas).batches)≤w/2:=by
  let N:=Receiver.arityLimit (v).middle.rootDegree (2^(v).middle.rootDepth) (v).front.donor.cap
    (v).middle.rotorBits (v).middle.rootDepth
  have key:=selected ((v).middle.rootField*N) (by simp [ResetOutput.rootUnits,N])
  have output:=selected (v).rootOutputBits (by simp [ResetOutput.rootUnits])
  have size : (atlas).instructionBits*(atlas).batches≤(v).rootOutputBits := by
    change DescentPackedResetRotorRoles.roleBits n * (DescentRecordedRotorLayers.layers n packet f ((2*cap)/2) *
      ResetInput.calendarLanes S G.b (age+1)) ≤ ResetMiddle.rootWord board k Ht f cap C packet
        (DescentPackedResetRotorRoles.roleBits n) (DescentRecordedRotorLayers.layers n packet f cap * ResetInput.calendarLanes S G.b (age+1))
    rw [show (2*cap)/2=cap by omega]
    exact (Nat.le_max_right ..).trans (Nat.le_max_left ..)
  have actualDegree : input.placement.degree=venue.degree:=input.branch.trans degreeAt.symm
  have width : DescentIssuedRotorRoles.guardInputs input.placement.degree (2^((Z).k-B.terminals.commonDepth))
        input.placement.cap≤N:=by
    rw [actualDegree,ClosedReset.Window.calendar_residual B,capAt]
    exact Nat.le_max_left ..
  have lanes:(v).receiver.lanes=2^e:=pitch
  rw [←lanes,Nat.mul_comm,max_mul]
  exact (max_le ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ width)).trans key)
    ((Nat.mul_le_mul_right _ size).trans output)).trans (Nat.div_le_div_right machine)


open DescentSixParty.ClosedReset.Window
local notation "res" => B.reset.k-B.terminals.commonDepth
local notation "fw" => (v).middle.rootField
local notation "nb" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "incoming" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

include capAt in
/-- All shape, capacity and frequency constraints of the original gate reader come
from the accounted previous census and the named date's packet width. -/
theorem fromNamed_original_limits (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) :
    max (max res (2^B.reset.n)) (2^res)<2^fw ∧ B.reset.n<fw ∧ res+1<2^fw ∧
    input.placement.cap<2^fw ∧ 2*k+n+2≤fw ∧ res<2^nb ∧ 1<2^nb ∧ 2^res*incoming<2^nb ∧
    2*DescentFallbackShapeTable.rows res (2^B.reset.n)≤2^(2*k+n+2) ∧ 0<quota S.rounds :=by
  have rootWidth : fw = ResetMiddle.fieldWidth venue.degree cap n k Ht := rfl
  rw [calendar_residual B,B.dimension,rootWidth]
  let field := ResetMiddle.fieldWidth venue.degree cap n k Ht
  have kb:k+1≤field:=(Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have nn:n+1≤field:=(Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have big:ResetMiddle.senderWidth k n Ht cap≤field:=(Nat.le_max_right ..).trans
    ((Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))
  have signed:2*k+n+2≤field:=by unfold ResetMiddle.senderWidth at big;omega
  have bw:2^n<2^field:=Nat.pow_lt_pow_right (by decide) (by omega)
  have kw:2^k<2^field:=Nat.pow_lt_pow_right (by decide) (by omega)
  have scope:Nat.clog 2 (input.placement.cap+1)≤field:=by
    rw [capAt]
    exact (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))
  have capWidth:=((Nat.lt_succ_self input.placement.cap).trans_le (Nat.le_pow_clog (by decide) _)).trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) scope)
  obtain ⟨base,one,mass,shape⟩:=named_census_packet_limits B p gr fee branch
  exact ⟨max_lt (max_lt (Nat.lt_two_pow_self.trans kw) bw) kw,by omega,
    kb.trans_lt Nat.lt_two_pow_self,capWidth,signed,base,one,mass,shape,Nat.succ_pos _⟩


/-- Both casts of the original chosen schedule use the same final receiver address. -/
theorem fromNamed_register_end :
    (im).receiver.preparedEnd (im).book=(rc).preparedEnd book:=(X₀).end_reindex ..

theorem fromNamed_register_groups : S.groupCount (age+1)*2^k=2^(T).commonDepth :=by
  rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix]

open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "stRun" => (a).throughStencil (u).shape start (u).count (u).hub (u).g (u).Y (u).src (u).sourceRows (u).oldDegree w
local notation "stTime" => (a).throughStencilTicks (u).shape start (u).count (u).hub (u).g (u).Y (u).sourceRows (u).oldDegree w

theorem FinalInputs.fromNamed_register_frame (z₀ : (u).FinalInputs) (ready : (u).Ready) (safe : z₀.Room)
    {before measured after : Memory w} (initialRun : (stRun).Exec before measured stTime)
    (spent : (u).throughOperandDate.Runs before after) :
    ∀addr,addr<(im).receiver.preparedEnd (im).book→
      z₀.classImage after addr=(im).receiver.preparedImage (im).book (im).prepared measured addr :=by
  have top:=fromNamed_register_end (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
  have value:=fromNamed_root_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt measured
  intro addr valid
  apply (z₀.reached_guard_frame ready safe initialRun spent addr (valid.trans_eq top)).trans
  exact (congrFun value.2.2.2.2.2 addr).symm

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
