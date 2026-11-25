import OAI.Hierarchy.DescentProfiledOuterTail
import OAI.Hierarchy.DescentProfiledRegisteredInputPrice

namespace OAI
/-! # The original two register readers and four final phases of each selected ordinary date -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler TerminalScale Chronology DescentInitialHost DescentResetInvoice
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {G : PoweredGadget F} {n d : ℕ} {board : NonlinearExpanders.Graph n d}
  {op : RotorSpec} {t f g reset τ drift degreeMax B h : ℕ}
  (x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h)
local notation "J" => Nat.log 2 h/(2*B)
local notation "z" => x.slot
local notation "Sx" => stageNumbers G t J f g reset (z).sites (tail τ J)
local notation "prior" => (z).position.ports
local notation "entry" => x.base.registeredEntry prior x.stageFloor
local notation "seedRate" => (NativePitch.FundedBase.public_rate G t f g reset).choose

theorem chosen_outer_return {driftR slots ratio argRead roleRead : ℕ}
    (buy : PitchCalendar.Purchased G board op t f g reset drift driftR degreeMax slots ratio τ B h)
    (driftPaid : drift+1≤ scale J driftR) (stock : 2^h≤2*(z).sites)
    (bus : (z).bus≤ratio*h)
    (pitches : (prior).ArchivePitchRoom ((Sx).groupCount (z).age) h (scale J argRead) (scale J roleRead))
    (saving : ℕ) (room : x.CodeRoom) :
    x.model.inputFee entry x.stageFloor (z).bus ≤
      x.Price (65*ratio) (inputReadRate G t f g reset driftR seedRate (max argRead roleRead)) 0 saving ∧
    x.lastInvoice room ≤ x.Price (ratio+1) (outerTailRate G t f g reset driftR) 0 saving :=
  ⟨x.registered_input_price buy driftPaid stock bus pitches saving x.stageFloor,
    x.registered_tail_price buy driftPaid stock bus saving room⟩

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
