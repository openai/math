import OAI.Hierarchy.TaggedSortLiftVolume
import OAI.Hierarchy.DescentTerminalSortTrace

namespace OAI
/-! # Volume of the installed physical sort bank for any dyadic terminal array -/

namespace Hierarchy.DescentTerminalHost.SortBank
open Tagged.SortLift

theorem physical_volume {steps : ℕ} (n h e : ℕ) (stages : Fin steps→Stage (2^e))
    (half : ∀ i j,2^n≤2*(stages i).length j) (rounds : steps≤4^7) :
    localCount stages*2^n+2^h ≤ (2*4^7+1)*(2^e+2^h) :=
  Tagged.SortLift.physical_volume n h e stages half rounds


end Hierarchy.DescentTerminalHost.SortBank

end OAI
