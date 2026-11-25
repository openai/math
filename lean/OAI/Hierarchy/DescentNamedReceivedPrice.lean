import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentResetIssuedSenderPrice

namespace OAI
/-! The physical schedule actually retains the atlas's shared operand bank. Its
dependent old-capacity cast does not change any instruction of a sender expression. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks
private theorem cast_sender {D k cap bound n : ℕ} (eqn : cap=bound) (old : EarlierBanks D k cap n)
    (u : ℕ) (room : (∀j,(old.donor.board j).work ≤ u) ∧ old.donor.host.work ≤ u ∧ old.donor.ones.work ≤ u) :
    let new : EarlierBanks D k bound n := (congrArg (fun t=>EarlierBanks D k t n) eqn).mp old
    (∀j,(new.donor.board j).work ≤ u) ∧ new.donor.host.work ≤ u ∧ new.donor.ones.work ≤ u := by
  cases eqn
  exact room
end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : Dated.Operands) (floor w : ℕ)
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
variable (fitsStencil : e ≤ laneBits (S.groupWidth k tail age + k) payload
    (S.localWalshBits p (S.groupWidth k tail age + k) f (quota S.rounds)) - k)
  (fitsSigned : e ≤ previous) (fitsCut : previous ≤ S.groupWidth k tail age) (count : Bank)
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

local notation "actual" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "limit" => CandidateFront.sourceLimit (v).front.peer.shapes (500+23*(P).S.m+64)

theorem named_operand_price :
    (v).front.OperandPrice ((v).issuedScene base₀ actual) limit := by
  let code : DescentResetHostSize.Code k:=⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let page : DescentSixParty.Chronology.RootPage k (2^n):=(false,.inr (code,none))
  let src:=(rc).atlasSources E (P).S (P).X (P).base (P).bank g (atlas).directions (atlas).hostIndex (.lit ((a).c/2))
    (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports (atlas).board (atlas).packet
    (atlas).C (atlas).groupDigits (atlas).batches (atlas).layerBits (atlas).factor (atlas).primitive page
  let raw:=CandidateFront.EarlierBanks.fromRoot rc book src (atlas).hostIndex io.hubs
    ((v).actor.directory actorBase) ((v).actor.scene actorBase)
  have half : (a).c/2=cap:=by change (2*cap)/2=cap;omega
  let registered : CandidateFront.EarlierBanks venue.degree k cap n:=
    (congrArg (fun t=>CandidateFront.EarlierBanks venue.degree k t n) half).mp raw
  let dir:=(v).actor.directory actorBase
  have rows:=(rc).issued_matrix_work E (P).S (P).X (P).base (P).bank g (atlas).directions (atlas).hostIndex
    (.lit ((a).c/2)) (a).depthCut (a).classBound (a).fullBudget (P).S.total (a).ports (atlas).board
    (atlas).packet (atlas).C (atlas).groupDigits (atlas).batches (atlas).layerBits (atlas).factor (atlas).primitive page (S.hostSize age)
  have priced:=CandidateFront.EarlierBanks.sender_limit rc book src (atlas).hostIndex io.hubs dir ((v).actor.scene actorBase) _ rows
  have exactRows:=CandidateFront.EarlierBanks.cast_sender half raw _ priced
  have small : Projected.Receiver.readWork (P).S.m (P).X.count (.lit ((a).c/2))+64 ≤500+23*(P).S.m+64 := by
    change 400+23*(P).S.m+(1+5)+1+64 ≤ _
    omega
  exact CandidateFront.original_price S board k tail age venue.degree f g (2^e) M
    (ResetMiddle.fieldWidth venue.degree cap n k Ht) ((v).front.metaBits) C packet cal early registered
    dir.flags dir.count dir.inverse _ (fun j=>(exactRows.1 j).trans small) (exactRows.2.1.trans small)
    (exactRows.2.2.trans small)

theorem named_received_price
    (ok : (v).front.SceneRoom early ((v).issuedScene base₀ actual) w) :
    let receipt:=(v).front.received early ((v).issuedScene base₀ actual) ok
    receipt.ticks+7*DescentStaticWordColumn.names receipt.program ≤ (v).front.receivedBill early limit :=
  (v).front.received_price early _ ok limit (named_operand_price G S board k tail age p f g drift degree payload
    e previous M nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)
    (Nat.two_pow_pos e)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
