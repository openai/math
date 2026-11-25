import OAI.Hierarchy.DescentProfiledOfferInvoice
import OAI.Hierarchy.DescentNamedFundedBaseWidth
import OAI.Hierarchy.DescentPaidPitchCalendar

namespace OAI
/-! # The original purchased input and date quantum on an ordinary offer -/
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
local notation "seats" => (z).menu.seats (z).age

theorem grain_positive : 0<(z).p:=by
  have value:=x.cut.ticket.grain_on_cut x.cut.before x.cut.after x.cut.joined x.cut.branch.issuedGrains
  have pos:=x.cut.input.unitPos
  by_contra! hz
  have zero : (z).p=0:=Nat.eq_zero_of_le_zero hz
  rw [value,DescentCompiler.AtomSchedule.grainAt,zero,Nat.zero_mul] at pos
  omega

theorem live_hosts (stock : 2^h≤2*(z).sites) : 0<(Sx).hostSize (z).age :=by
  have pos:=Nat.two_pow_pos h
  have site : 0<(z).sites:=by omega
  change 0<(z).sites*(2^(Sx).hostGain*(Sx).radix)^(z).age
  exact Nat.mul_pos site (pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (by rw [x.cut.radix];positivity)) _)

theorem offered_base_width {driftR : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ B drift driftR degreeMax h) :
    x.base.fundedMaxUnit 0 ≤ scale J (NativePitch.FundedBase.public_rate G t f g reset).choose :=
  Branch.registered_base_width x.cut.original G Sx x.cut.branch x.cut.ticket x.cut.before x.cut.after
    x.cut.joined op tb drift (z).degree h seats (prior).venue.lanes prior (prior).io.roster
    (z).menu.ordinary grant rfl rfl (z).grainLimit

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
