import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentResetOperandSetup

namespace OAI
/-! Dimensions and bounds of the actual old/fresh query selector in the named physical reset. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty DescentResetLocalRoster ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet : ℕ) (old : Prior) (base : ℕ)
local notation "v" => fromBoard G S board k tail age p f g drift degree payload e previous M nextM C packet old base
local notation "A" => (v).receiver
local notation "T" => (v).setup
local notation "height" => GroupStage.depthBound old.venue.degree n f g
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256

theorem named_ticket_shape :
    (A).hosts=(T).placement.newHosts ∧ (A).groups=(T).placement.groups ∧
      (T).queryBits=(A).queryBits ∧ (T).lanes=(A).lanes ∧
      (A).valueBits=DescentOperandWidth.recordBits G S k tail drift degree p ∧
      (T).cable.units=ResetInput.calendarLanes S G.b (age+1) ∧
      (A).candidates=publicSlots board height k cap :=⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem named_ticket_limits :
    2*(A).candidates<2^(A).queryBits ∧ 1+2*(T).cable.strip≤2*(A).candidates ∧
    DescentOperandWidth.s G S k tail drift degree≤(T).cable.fieldBits :=by
  let total:=publicSlots board height k cap
  have fibre : (T).retained.donors = 2^k := by
    let c := S.groupWidth k tail age
    let shift := S.retainedExponent G k tail drift degree p age payload
    have bound : shift ≤ c := Nat.min_le_left ..
    change 2^(c-shift+(shift+k)-c) = 2^k
    congr 1
    omega
  refine ⟨?_, ?_, ?_⟩
  · change 2*total < 2^(Nat.clog 2 (2*total+1))
    exact Nat.lt_of_succ_le (Nat.le_pow_clog (by decide : 1<2) (2*total+1))
  · change 1+2*((T).retained.donors*(2*cap)) ≤ 2*total
    rw [fibre]
    dsimp only [total,publicSlots]
    omega
  · exact (Nat.le_max_left ..).trans (Nat.le_max_left ..)
end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
