import OAI.Hierarchy.DescentResetAtlasTraffic
import OAI.Hierarchy.DescentResetClippedDatePrice

namespace OAI
/-! Converting the native atlas word bill into a dated bit bill at the physical clipped pitch. -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section

/-- The first summand pays one original host. The second pays one original group
at its real clipped output pitch. Shared lookups are charged once for all hosts. -/
theorem atlas_date_price (D n Ht rate receiver ratio saving : ℕ) :
    ∃C exponent : ℕ,∀ᶠ h : ℕ in atTop,∀ J hst groups stages copies u N b width rows w fee : ℕ,
      J ≤ Nat.log 2 h → 2^h ≤ copies → u ≤ scale J rate → N ≤ scale J rate →
      b ≤ scale J rate → width ≤ scale J receiver → w ≤ ratio*h →
      rows*h ≤ (2+N)*h+groups*(32*N*b+16*width) →
      fee ≤ (rootCoefficient D n Ht u).total 1 1 1*(hst+hst*rows+(h+1)*2^(h/2)) →
      1 ≤ stages →
      fee*w ≤ hst*h*(C*scale J exponent)+hst*(groups*stages)*(C*scale J exponent)+copies/(2^J)^saving := by
  obtain ⟨lead,price,limit⟩:=coefficient_scale D n Ht rate
  obtain ⟨c,e,late⟩:=clipped_date_price lead price 1 rate receiver ratio saving
  refine ⟨c,e,?_⟩
  filter_upwards [late] with h paid
  intro J H G δ copies u N b width rows w fee Jle ambient uFit cells walsh field word packed charge radix
  apply paid J H G δ copies ((rootCoefficient D n Ht u).total 1 1 1) N b width rows w fee Jle ambient
    (limit J u uFit) cells walsh field word packed _ radix
  simpa only [pow_one] using charge

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
