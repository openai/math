import OAI.Computability.VPVNP.SliceArithmeticCallClear
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-! # Appending a high zero bit to a physical RAM operand

Every read/write sort pair uses an extra phase bit in its address ordinal. The
ordinary RAM still has its full address space. Before staging the five sorter
words, a fixed table overwrites each scratch copy of a RAM operand by its exact
zero extension. Both the source and all unrelated stacks are preserved.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamProbeEmit

open VPVNP RAMTape SuccessorFields SliceArithmetic.CallClear

variable {K : Type} [DecidableEq K]

/-- Clear the old copy, push its high zero, then prepend the low bits of the unchanged source. -/
def extendWord (src dst tmp : K) : FiniteRoutine K :=
  ((clear dst).followedBy (FiniteRoutine.ofRoutine (Routine.push dst false))).followedBy
    (prependCopy src dst tmp)

/-- Bit-exact zero extension. The width of the RAM word affects only the execution time. -/
theorem extendWord_runs (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : Stacks K) (hs : s tmp = []) :
    (extendWord src dst tmp).Runs ((s dst).length + 5*(s src).length + 4) s
      (Function.update s dst (s src ++ [false])) := by
  let u := Function.update s dst []
  let v := Function.update s dst [false]
  have a := clear_runs dst s
  have b : (FiniteRoutine.ofRoutine (Routine.push dst false)).Runs 1 u v := by
    change (Routine.push dst false).Runs _ _ _
    simpa [u, v, Function.update_idem] using Routine.runs_push dst false u
  have c := prependCopy_runs src dst tmp hsd hst hdt v (by simpa [v, hdt.symm] using hs)
  simpa only [extendWord, u, v, Function.update_of_ne hsd, Function.update_self, Function.update_idem,
    show (s dst).length+1+1+(5*(s src).length+2) = (s dst).length+5*(s src).length+4 by omega] using
      (a.followedBy b).followedBy c

/-- Straight-line table of zero extensions, one per operand. -/
def extendAll {ι : Type} (tmp : K) (src dst : ι → K) : List ι → FiniteRoutine K
  | [] => .ret
  | k :: ks => (extendWord (src k) (dst k) tmp).followedBy (extendAll tmp src dst ks)

end TeamProbeEmit

end BorderVNP
end Computability
end OAI
