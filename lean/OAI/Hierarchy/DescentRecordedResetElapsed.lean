import OAI.Hierarchy.DescentResetSlotIndex
import OAI.Hierarchy.DescentResetSplicePrice

namespace OAI
/-! # Every recorded reset follows an ordinary round in a shrinking epoch -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentResetInvoice

theorem rounds_pos_of_shrink {h C rounds : ℕ} {ρ : ℝ}
    (shorten : reentryRate h C*ρ^rounds≤1/2) : 0< rounds := by
  by_contra hz
  have zero : rounds=0 := by omega
  rw [zero,pow_zero,mul_one] at shorten
  have nonneg : 0≤ internalRate h C := by unfold internalRate; positivity
  unfold reentryRate splicedRate at shorten
  linarith

theorem elapsed_at_reset {h C rounds height age : ℕ} {ρ : ℝ}
    (shorten : reentryRate h C*ρ^rounds≤1/2)
    (entry : ((kindCalendar rounds height).drop age).head?=some true) : 0< age := by
  have place := reset_slot_index rounds height age entry
  have positive := rounds_pos_of_shrink shorten
  have le : age%(rounds+1)≤ age := Nat.mod_le _ _
  omega

end Hierarchy.DescentSixParty.Chronology

end OAI
