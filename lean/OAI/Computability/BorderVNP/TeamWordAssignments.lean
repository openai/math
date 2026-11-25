import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.SliceArithmeticCallClear

/-! # Overwriting words between the RAM registers and physical probe slots

Clearing the destination and prepending a preserved source copies one complete word in
its original little-endian order. Sequencing the copies leaves the common scratch empty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamWords

open VPVNP.RAMTape VPVNP.SliceArithmetic.CallClear

variable {K : Type} [DecidableEq K]

/-- Overwrite a separate destination by the complete source word. -/
def assign (src dst tmp : K) : FiniteRoutine K :=
  (clear dst).followedBy (SuccessorFields.prependCopy src dst tmp)

/-- A complete copy is linear in the old destination length and source word width. -/
theorem assign_runs (src dst tmp : K) (hd : src ≠ dst) (ht : src ≠ tmp) (dt : dst ≠ tmp)
    (s : Stacks K) (blank : s tmp = []) :
    (assign src dst tmp).Runs ((s dst).length + 5*(s src).length + 3) s
      (Function.update s dst (s src)) := by
  have a := clear_runs dst s
  have b := SuccessorFields.prependCopy_runs src dst tmp hd ht dt (Function.update s dst [])
    (by simpa [dt.symm] using blank)
  simpa only [assign, Function.update_of_ne hd, Function.update_self, Function.update_idem, List.append_nil,
    show (s dst).length + 1 + (5*(s src).length+2) = (s dst).length+5*(s src).length+3 by omega] using
    a.followedBy b

end TeamWords

end BorderVNP
end Computability
end OAI
