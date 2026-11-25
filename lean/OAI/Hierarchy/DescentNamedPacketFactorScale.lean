import OAI.Hierarchy.DescentNamedPacketVolume
import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentPacketFactorRate
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
/-! # The two actual packet stages have a fixed-exponent date price -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty
noncomputable section

set_option maxRecDepth 16384 in
theorem fromBoard_packet_factor {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet : ℕ) (old : Prior) (base rate j growth : ℕ)
    (window : 2^k≤ scale j rate)
    (capacity : ((capCalendar G.b S.rounds g S.height).take age).prod*256 ≤ scale j rate)
    (stage : growth≤ scale j rate) :
    (fromBoard G S board k tail age p f g drift degree payload e previous M nextM C packet old base).packetFactor growth ≤
      packetRateLead old.venue.degree n*scale j (5*rate) :=
  packet_factor_le old.venue.degree n rate j k _ growth window capacity stage

open DescentNamedFundedChart Filter

set_option maxRecDepth 16384 in
/-- The exponent and leading coefficient are fixed before the residual calendar and its
packing denominator. The field bounds follow from the same receipt as the host census. -/
theorem fromBoard_packet_at {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F)
    (board : NonlinearExpanders.Graph n d) (t f g reset D τ B : ℕ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop,∀ copies age p e prev M nextM C packet drift degree base : ℕ, ∀old : Prior,
      p≤h → old.venue.degree=D →
      let j:=Nat.log 2 h/(2*B)
      let sched:=stageNumbers G t j f g reset copies (TerminalScale.tail τ j)
      let k:=groupBits t j sched.hostGain sched.capGain (cutRate t f g)
      let v:=fromBoard G sched board k (TerminalScale.tail τ j) age p f g drift degree h e prev M nextM C packet old base
      v.packetFactor (2^sched.hostGain*sched.radix)≤packetRateLead D n*scale j (5*ResetMiddle.receiptLocalRate G board t f g reset D) := by
  filter_upwards [ResetMiddle.receipt_controls_at G board t f g reset D τ B den] with h control
  intro copies age p e prev M nextM C packet drift degree base old hp hD j sched k v
  obtain ⟨window,capacity,_,growth,_⟩:=control copies age p e prev hp
  have bound:=fromBoard_packet_factor G sched board k (TerminalScale.tail τ j) age p f g drift degree h
    e prev M nextM C packet old base (ResetMiddle.receiptLocalRate G board t f g reset D) j
    (2^sched.hostGain*sched.radix) window capacity growth
  simpa only [hD] using bound

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
