import OAI.Hierarchy.DescentProfiledOuterSource
import OAI.Hierarchy.DescentProfiledOrdinaryCharges
import OAI.Hierarchy.DescentNamedRegisteredSuffix

namespace OAI
/-! # Return tariff of the attained venue, metadata, seven final fields and retained pair count -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler TerminalScale Chronology DescentInitialHost DescentResetInvoice
open DescentPacking.PackedMatch.Local.Stage DescentDatedAddressBook
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] {G : PoweredGadget F} {n d : ℕ} {board : NonlinearExpanders.Graph n d}
    {op : RotorSpec} {t f g reset τ drift degreeMax B h : ℕ}
local notation "idx" H:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B H
local notation "J" => Nat.log 2 h/(2*B)
local notation "tb" => tail τ J
variable (x : idx h)
local notation "z" => x.slot
local notation "sx" => stageNumbers G t J f g reset (z).sites tb
local notation "ports" => (z).position.ports
local notation "seats" => (z).menu.seats (z).age

def outerTailRate (G : PoweredGadget F) (t f g reset driftR : ℕ) :=
  let seedRate:=(NativePitch.FundedBase.public_rate G t f g reset).choose
  returnDateRate G t f g reset driftR (44*argumentDigitRate G t f g reset driftR seedRate)

theorem registered_tail_price {driftR slots ratio : ℕ}
    (buy : PitchCalendar.Purchased G board op t f g reset drift driftR degreeMax slots ratio τ B h)
    (driftPaid : drift+1≤ scale J driftR) (stock : 2^h≤2*(z).sites) (bus : (z).bus≤ratio*h)
    (saving : ℕ) (room : x.CodeRoom) :
    x.lastInvoice room≤x.Price (ratio+1) (outerTailRate G t f g reset driftR) 0 saving :=by
  let E:=outerTailRate G t f g reset driftR
  have live:=x.live_hosts stock
  have bill:=Branch.named_registered_paid x.cut.original G sx x.cut.branch x.cut.ticket
    x.cut.before x.cut.after x.cut.joined op tb drift (z).degree h seats (ports).venue.lanes ports
    (ports).io.roster (z).menu.ordinary x.stageFloor buy.old buy.returned rfl rfl rfl driftPaid
    (x.offered_base_width buy.old) (z).degreeLimit (z).grainLimit x.firstWidth
    (z).geometry.room.archive (z).geometry.room.args x.grain_positive stock live (fun _ _ _=>⟨rfl,rfl⟩)
    x.stageFloor (z).bus (x.model.reachedSources x.stageFloor) room.result bus
  change x.lastInvoice room≤(sx).hostSize (z).age*h*(ratio*scale J E+1)+
    (sx).hostSize (z).age*((sx).groupCount (z).age*(sx).radix)*(ratio*scale J E) at bill
  have scalePos:0<scale J E:=Nat.two_pow_pos _
  have left : ratio*scale J E+1≤(ratio+1)*scale J E:=by rw [Nat.add_mul,Nat.one_mul];omega
  have right : ratio*scale J E≤(ratio+1)*scale J E:=by rw [Nat.add_mul,Nat.one_mul];omega
  apply bill.trans
  simp only [Price,Nat.zero_mul,Nat.add_zero]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ left) (Nat.mul_le_mul_left _ right)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
