import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.OracleSpec.BitStack
import OAI.Optimization.LinearProgramming.PriceGame.Moment

/-! Compilation of the rational score ceiling in Section 5. The program uses
finite Boolean stacks, rational arithmetic, a sign test and a signed ceiling. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- Truncate negative signed integers to zero and expose the binary magnitude otherwise. -/
noncomputable def intToNatP : Procedure intCode Nat.bits Int.toNat :=
  (conditional intSign (constant intCode Nat.bits 0) intAbs).congrFun (by
    intro z; cases z <;> simp)

/-- Compute the natural ceiling on the entire rational input domain. -/
noncomputable def ratNatCeilP : Procedure ratCode Nat.bits (fun q : ℚ => ⌈q⌉₊) :=
  (intToNatP.comp OracleSpec.Arithmetic.ratCeil).congrFun (by intro q; exact Int.ceil_toNat q)

/-- Clamp the input below at zero before scaling the score. -/
noncomputable def ratMaxZeroP : Procedure ratCode ratCode (fun q : ℚ => max 0 q) := by
  let z := constant ratCode ratCode (0 : ℚ)
  let q := identity ratCode
  apply (conditional (OracleSpec.Arithmetic.ratLe.comp (z.pair q)) q z).congrFun
  intro x
  change (if decide (0 ≤ x) then x else 0) = max 0 x
  by_cases hx : 0 ≤ x
  · simp [hx]
  · simp [hx, max_eq_left (le_of_not_ge hx)]

/-- Fixed rational constants are serialized literally by the constant procedures.
Input is the signed, reduced rational mean of the expert and output is its binary score. -/
noncomputable def scoreP : Procedure ratCode Nat.bits (Moment.rationalScore Moment.scaleQ Moment.sigmaQ) := by
  let shift := ratSub.comp ((identity ratCode).pair (constant ratCode ratCode (Moment.sigmaQ / 2)))
  let positive := ratMaxZeroP.comp shift
  let scaled := ratMul.comp ((constant ratCode ratCode Moment.scaleQ).pair positive)
  exact (ratNatCeilP.comp scaled).congrFun (fun _ => rfl)

theorem scoreP_runs (q : ℚ) :
    ∃ steps ≤ scoreP.bound.eval (ratCode q).length,
      Runs scoreP.program (singletonStore scoreP.input (ratCode q))
        (singletonStore scoreP.output (Moment.rationalScore Moment.scaleQ Moment.sigmaQ q).bits) steps :=
  scoreP.runs q

theorem scoreP_output_length (q : ℚ) :
    (Moment.rationalScore Moment.scaleQ Moment.sigmaQ q).bits.length ≤
      (ratCode q).length + scoreP.bound.eval (ratCode q).length :=
  scoreP.output_length_le q

/-- The score computation embeds in the oracle machine at the same step count and
preserves its buffered output and transcript. -/
theorem scoreP_exec {k : ℕ} (embed : scoreP.K ↪ Fin k) (base : Store (Fin k)) (answer : Fin k)
    (o : OracleSpec.WordOracle) (buf : OracleSpec.Word) (hist : OracleSpec.Transcript) (q : ℚ) :
    ∃ steps ≤ scoreP.bound.eval (ratCode q).length,
      OracleSpec.BitCode.Executes answer o (OracleSpec.BitCode.ofBitStack (scoreP.program.relabel embed))
        ⟨overlay embed base (singletonStore scoreP.input (ratCode q)), buf, hist⟩
        ⟨overlay embed base (singletonStore scoreP.output (Moment.rationalScore Moment.scaleQ Moment.sigmaQ q).bits),
          buf, hist⟩ steps :=
  OracleSpec.BitCode.procedure_exec scoreP embed base answer o buf hist q

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
