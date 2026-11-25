import OAI.Hierarchy.DescentNamedTicketGeometry
import OAI.Hierarchy.DescentNamedIssuedOrdinal

namespace OAI
/-! Native extent of the query and candidate lookup pages and the kept-field cast table. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentOperandCandidateLookup
private theorem exponent_le (n w : ℕ) (room : 2^n<2^w):n≤w:=by
  by_contra! large
  exact (Nat.pow_le_pow_right (by decide : 0<2) large.le).not_gt room

theorem physical_operand_rooms (v : ResetOutput) (base w : ℕ) (live : 0<2*v.receiver.candidates)
    (field : v.receiver.valueBits≤v.setup.fieldBits) (room : v.finalEnd base<2^w) :
    v.receiver.queryBits*v.receiver.lanes≤w ∧
    v.receiver.valueBits*v.receiver.lanes≤w ∧ v.receiver.signedBits*v.receiver.lanes≤w:=by
  let A:=v.receiver
  have ends:=v.operand_order base
  have last_:= (v.final_ge base).trans_lt room
  have key : 2^((A.queryBits+A.signedBits)*A.lanes)<2^w:=by
    apply Nat.lt_of_le_of_lt _ (ends.2.trans_lt last_)
    change _≤v.operandStart base+((2*A.candidates)*2)*2^((A.queryBits+A.signedBits)*A.lanes)
    exact (Nat.le_mul_of_pos_left _ (Nat.mul_pos live (by decide))).trans (Nat.le_add_left ..)
  have castPage : 2^(v.setup.fieldBits*A.lanes)<2^w:=by
    apply Nat.lt_of_le_of_lt _ (ends.1.trans_lt (ends.2.trans_lt last_))
    change _≤v.keepBase base+1*(2*2^(v.setup.fieldBits*A.lanes))
    omega
  have both:=exponent_le _ _ key
  rw [Nat.add_mul] at both
  exact ⟨(Nat.le_add_right ..).trans both,
    (Nat.mul_le_mul_right _ field).trans (exponent_le _ _ castPage),(Nat.le_add_left ..).trans both⟩

end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
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
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "I" prepared:arg scene:arg => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial prepared scene

open DescentPackedZip DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
local notation "P₀" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "A" => (v).receiver
set_option maxHeartbeats 800000 in
theorem DateInputs.named_amount_rooms (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ready : (I prepared scene).Ready) :
    (A).queryBits*(A).lanes≤w ∧ (I prepared scene).operand.coeff*(A).lanes≤w ∧ (A).signedBits*(A).lanes≤w:=by
  have small:=ResetOutput.named_ticket_limits G S board k tail age p f g drift degree payload e previous M nextM C
    packet P₀ base₀
  have stage := named_successor G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor
  have bound : 1+2*(v).setup.cable.strip≤2*(A).candidates := by
    rw [stage]
    exact small.2.1
  have nonempty : 0<2*(A).candidates := (Nat.add_pos_left (by decide : 0<1) _).trans_le bound
  have valueFits : (A).valueBits≤(v).setup.fieldBits := by
    rw [stage]
    exact Nat.le_max_left ..
  exact (v).physical_operand_rooms base₀ w nonempty valueFits ready.full

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
