import OAI.Hierarchy.DescentDatedCanonicalFront
import OAI.Hierarchy.DescentResetRankFunctions
import OAI.Hierarchy.DescentResetMiddleCalendar

namespace OAI
/-! # Physical field widths for the reset's relative endpoint and census tables -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty DescentCompiler DescentDenseHostOrder DescentResetLocalRoster
noncomputable section
set_option quotPrecheck false
def endpointWidth (degree shapes nextCap : ℕ) :=
  max (fieldBits nextCap) (Nat.clog 2 (degree+2)+Nat.clog 2 (shapes+1))

theorem endpoint_room (degree shapes nextCap : ℕ) (j : Fin shapes) (s : Fin (degree+1)) :
    j.val*2^Nat.clog 2 (degree+2)+(s.val+1)<2^endpointWidth degree shapes nextCap := by
  have digit : s.val+1<2^Nat.clog 2 (degree+2):=(show s.val+1<degree+2 by omega).trans_le
    (Nat.le_pow_clog (by decide) _)
  have cells : shapes<2^Nat.clog 2 (shapes+1):=(Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _)
  calc
    _ < (j.val+1)*2^Nat.clog 2 (degree+2) := by rw [Nat.add_mul,Nat.one_mul];omega
    _ ≤ (2^Nat.clog 2 (shapes+1))*2^Nat.clog 2 (degree+2) :=
      Nat.mul_le_mul_right _ ((Nat.succ_le_of_lt j.isLt).trans cells.le)
    _ = 2^(Nat.clog 2 (degree+2)+Nat.clog 2 (shapes+1)) := by rw [pow_add,Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.le_max_right ..)

variable {n h : ℕ} (S : AtomSchedule) (board : NonlinearExpanders.Graph n h)
    (k tail age D f g receiverBatch nextBatch C packet : ℕ) (calendar : List ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "cap" => (calendar.take age).prod*256
local notation "shapes" => (roster board k height).card
def menu : CandidateFront:=setupFront S board k tail age D f g receiverBatch nextBatch
    (ResetMiddle.fieldWidth D cap n k height) (endpointWidth D shapes (2^g*cap)) C packet calendar
local notation "A" => menu S board k tail age D f g receiverBatch nextBatch C packet calendar

theorem menu_fields :
    (A).privateBits=ResetMiddle.privateWidth board k height f cap C packet ∧
    (A).stemField=ResetMiddle.fieldWidth D cap n k height ∧
    fieldBits (2^g*cap)≤(A).metaBits := ⟨rfl,rfl,Nat.le_max_left ..⟩

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
