import OAI.Computability.BorderVNP.CubeDirectedIntervalInit
import OAI.Computability.BorderVNP.CubeDirectedIntervalPass

/-! # Setting up and running the directed interval pass on the real public frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Complete native program for the ordered-pair intervals at the beginning of Section 8.2. -/
def prepare : Code := .seq init cablePass

/-- Exact postcondition and a linear cost in the square label array and number of
cable descriptors. The cost is independent of the sum of the cable widths. -/
theorem run_prepare {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (hf : (pub 0).val = l.frame) (fields : l.Fields (readings m)) :
    BoundedRun pub macros prepare s m (setup.slots + (4*l.alphabet^2+2) + (2+l.count*(cableStep.slots+1)))
      (fun z => l.Ready z ∧ l.Image (readings m) l.count z.mem) := by
  apply (run_init pub macros l s m fit hf fields).seq
  intro u mu hu
  exact run_cablePass pub macros l (readings m) fit u mu hu.1 (by rw [show readings mu = _ from hu.2]; exact cleared_image l _)

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI
