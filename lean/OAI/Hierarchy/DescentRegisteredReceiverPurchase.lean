import OAI.Hierarchy.DescentRegisteredReceiverWidth
import OAI.Hierarchy.DescentPaidPitchCalendar

namespace OAI
/-! The pitch calendar pays for every reset receiver on the registered chronology. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook.PhysicalReset Filter

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset τ drift driftR bound quota B : ℕ)

theorem paid_receiver_calendar
    (fund : PitchCalendar.threshold G board op t f g reset drift driftR bound quota τ ≤ B) :
    ∀ᶠ h : ℕ in atTop, ReceiverCalendar G board op t f g reset τ drift bound B h := by
  unfold PitchCalendar.threshold at fund
  have branch : G.b ≤ 2^(capRate G t g) :=
    (show G.b ≤ capRate G t g by unfold capRate; omega).trans Nat.lt_two_pow_self.le
  exact receiver_calendar G board op t f g reset τ drift bound B (by omega) (by omega) branch

end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
