import OAI.Hierarchy.DescentProfiledOuterSource
import OAI.Hierarchy.DescentChosenRegisteredDate
import OAI.Hierarchy.DescentRegisteredInputHalfPage

namespace OAI
/-! # The two original register input scans on a concrete ordinary offer -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler TerminalScale Chronology DescentInitialHost DescentResetInvoice
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {G : PoweredGadget F} {n d : ℕ} {board : NonlinearExpanders.Graph n d}
    {op : RotorSpec} {t f g reset τ drift degreeMax B h : ℕ}
variable (x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h)
local notation "J" => Nat.log 2 h/(2*B)
local notation "tb" => tail τ J
local notation "z" => x.slot
local notation "Sx" => stageNumbers G t J f g reset (z).sites tb
local notation "prior" => (z).position.ports
local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g reset).choose

theorem registered_input_price {driftR slots ratio argRead roleRead : ℕ}
    (buy : PitchCalendar.Purchased G board op t f g reset drift driftR degreeMax slots ratio τ B h)
    (driftPaid : drift+1≤ scale J driftR) (stock : 2^h≤2*(z).sites) (bus : (z).bus≤ratio*h)
    (pitches : (prior).ArchivePitchRoom ((Sx).groupCount (z).age) h (scale J argRead) (scale J roleRead))
    (saving floor : ℕ) :
    x.model.inputFee (x.base.registeredEntry prior x.stageFloor) floor (z).bus ≤
      x.Price (65*ratio) (inputReadRate G t f g reset driftR baseRate (max argRead roleRead)) 0 saving := by
  have rooms := (z).geometry.room
  have reads:=pitches.inputPitch rooms.population.groups
  have mono {i j : ℕ} (v : i≤j) : scale J i≤ scale J j :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ v)
  have same : max (scale J argRead) (scale J roleRead)=scale J (max argRead roleRead) := by
    rcases le_total argRead roleRead with l|r
    · rw [max_eq_right l,max_eq_right (mono l)]
    · rw [max_eq_left r,max_eq_left (mono r)]
  rw [same] at reads
  have paid:=Branch.paid_registered_inputs x.cut.original G Sx x.cut.branch x.cut.ticket x.cut.before
    x.cut.after x.cut.joined op tb drift (z).degree h ((z).menu.seats (z).age) (prior).venue.lanes prior
    (prior).io.roster (z).menu.ordinary x.stageFloor buy.old buy.returned rfl rfl rfl driftPaid
    (x.offered_base_width buy.old) (z).degreeLimit (z).grainLimit x.firstWidth rooms.archive rooms.args
    x.grain_positive rooms.population reads floor (z).bus (x.live_hosts stock) bus
  have radix : 0<(Sx).radix := Nat.two_pow_pos _
  have grown : (z).sites≤(Sx).hostSize (z).age :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos _) radix))
  apply paid.trans
  simpa only [Price,Nat.mul_assoc,Nat.zero_mul,Nat.add_zero] using
    MaterialProgram.input_purchased_price h (z).sites ((Sx).hostSize (z).age) ((Sx).groupCount (z).age)
      (Sx).radix (ratio*scale J (inputReadRate G t f g reset driftR baseRate (max argRead roleRead))) stock grown radix

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
