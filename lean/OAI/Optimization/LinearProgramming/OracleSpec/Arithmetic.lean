import OAI.Computability.QuantumFactoring.BitStackGCD
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.BitStackRationalFloor

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace Arithmetic

open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure

/-- Comparison on signed integers using subtraction and the stored sign of its result. -/
noncomputable def intLt : Procedure (prodCode intCode intCode) boolCode
    (fun z => decide (z.1 < z.2)) :=
  (intSign.comp intSub).congrFun (by intro z; simp)

noncomputable def intLe : Procedure (prodCode intCode intCode) boolCode
    (fun z => decide (z.1 ≤ z.2)) :=
  (boolNot.comp (intLt.comp (swap intCode intCode))).congrFun (by
    intro z
    change (!decide (z.2 < z.1)) = decide (z.1 ≤ z.2)
    by_cases h : z.1 ≤ z.2
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h])

/-- The positive rational denominator ensures that the numerator detects sign. -/
noncomputable def ratLt : Procedure (prodCode ratCode ratCode) boolCode
    (fun z => decide (z.1 < z.2)) :=
  ((intSign.comp ratNum).comp ratSub).congrFun (by
    intro z
    change decide ((z.1 - z.2).num < 0) = decide (z.1 < z.2)
    apply decide_eq_decide.mpr
    rw [← not_le, Rat.num_nonneg, not_le, sub_neg])

noncomputable def ratLe : Procedure (prodCode ratCode ratCode) boolCode
    (fun z => decide (z.1 ≤ z.2)) :=
  (boolNot.comp (ratLt.comp (swap ratCode ratCode))).congrFun (by
    intro z
    change (!decide (z.2 < z.1)) = decide (z.1 ≤ z.2)
    by_cases h : z.1 ≤ z.2
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h])

noncomputable def ratCeil : Procedure ratCode intCode (fun q => ⌈q⌉) :=
  (intNeg.comp (ratFloor.comp ratNeg)).congrFun (by intro q; simp [Function.comp_def, Int.floor_neg])

end Arithmetic
end OracleSpec
end LinearProgramming
end Optimization
end OAI
