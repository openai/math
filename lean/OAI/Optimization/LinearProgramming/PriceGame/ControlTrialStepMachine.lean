import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepFeedback
import OAI.Optimization.LinearProgramming.OracleSpec.BitStack

/-! A uniform binary-stack compiler for the recursive scheduling transition. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire

/-- The finite physical control program receives its dimension, range, full expert roster,
and saved continuation stack as data. Its only fixed loop parameter is the probe count. -/
noncomputable def trialStepP (calls : ℕ) (ops : TrialGlobals → TrialKernel) (components : TrialKernelProcedures ops) :
    Procedure (prodCode trialGlobalsCode stateCode) trialActionCode (fun x => step (ops x.1) calls x.2) := by
  let inP := choosePacket (default : EnterData) (default : ScheduleData)
    (enterStepP calls ops components) (scheduleStepP calls ops components)
  let outP := choosePacket (default : PackedRound) ((blankTrialFrame, default, []) : FeedbackData)
    (returnedStepP calls ops) (feedbackStepP calls ops components)
  let control := choosePacket (.inl (default : EnterData)) (.inl (default : PackedRound)) inP outP
  let g := first trialGlobalsCode stateCode
  let s := second trialGlobalsCode stateCode
  let tag := trialTagP.comp (pcOfStateP.comp s)
  let stack := stackOfStateP.comp s
  apply (control.comp (tag.pair (g.pair stack))).congrFun
  rintro ⟨g,pc,stack⟩
  cases pc <;> rfl

/-- The bit-stack proof gives a polynomial runtime on every encoded input and a clean
output store containing precisely the encoded next transition. -/
theorem trialStepP_runs (calls : ℕ) (ops : TrialGlobals → TrialKernel)
    (components : TrialKernelProcedures ops) (g : TrialGlobals) (s : MachineState) :
    let p := trialStepP calls ops components
    ∃ k ≤ p.bound.eval ((prodCode trialGlobalsCode stateCode) (g,s)).length,
      Runs p.program (singletonStore p.input ((prodCode trialGlobalsCode stateCode) (g,s)))
        (singletonStore p.output (trialActionCode (step (ops g) calls s))) k :=
  (trialStepP calls ops components).runs (g,s)

theorem trialStepP_exec (calls : ℕ) (ops : TrialGlobals → TrialKernel)
    (components : TrialKernelProcedures ops) (k : ℕ) (embed : (trialStepP calls ops components).K ↪ Fin k)
    (base : Store (Fin k)) (answer : Fin k) (o : OracleSpec.WordOracle)
    (buf : OracleSpec.Word) (hist : OracleSpec.Transcript) (g : TrialGlobals) (s : MachineState) :
    let p := trialStepP calls ops components
    ∃ n ≤ p.bound.eval ((prodCode trialGlobalsCode stateCode) (g,s)).length,
      OracleSpec.BitCode.Executes answer o (OracleSpec.BitCode.ofBitStack (p.program.relabel embed))
        ⟨overlay embed base (singletonStore p.input ((prodCode trialGlobalsCode stateCode) (g,s))),buf,hist⟩
        ⟨overlay embed base (singletonStore p.output (trialActionCode (step (ops g) calls s))),buf,hist⟩ n :=
  OracleSpec.BitCode.procedure_exec (trialStepP calls ops components) embed base answer o buf hist (g,s)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
