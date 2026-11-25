import OAI.Optimization.LinearProgramming.PriceGame.ControlWireState
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine
import OAI.Computability.QuantumFactoring.BitStackSubtractor

/-! Bit-stack layouts and constructors for the explicit trial stack machine. The
public dimension is unary and the range and all price data are binary. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire

abbrev TrialGlobals := ℕ × ℕ × List PackedExpert
abbrev TrialKernel := Kernel NodeInput Prepared PackedRound Completed PackedQuery
abbrev TrialAction := Action NodeInput Prepared PackedRound Completed PackedQuery
abbrev TrialFrame := Frame NodeInput Prepared Completed
abbrev TrialPC := PC NodeInput Prepared PackedRound Completed

abbrev trialGlobalsCode : TrialGlobals → List Bool := prodCode unaryCode (prodCode Nat.bits (listCode packedExpertCode))
abbrev trialStackCode := listCode frameCode
abbrev trialRowsCode := listCode completedCode
abbrev trialResumeCode := prodCode packedQueryCode (prodCode stateCode stateCode)

def trialActionCode : TrialAction → List Bool
  | .proceed s => false :: stateCode s
  | .ask q f t => true :: false :: trialResumeCode (q,f,t)
  | .halt out => true :: true :: packedRoundCode out

abbrev trialCallDataCode := prodCode nodeInputCode trialRowsCode
abbrev trialFinishDataCode := prodCode nodeInputCode (prodCode trialRowsCode
  (prodCode preparedCode (prodCode packedRoundCode (id : List Bool → List Bool))))
abbrev trialFinishResultCode := sumCode completedCode packedQueryCode

/-- Finite code for the actual numerical operations. Every program takes the same
runtime globals. None of the programs or the public parameters are unrolled over
the dimension, range, number of experts, or depth. -/
structure TrialKernelProcedures (ops : TrialGlobals → TrialKernel) where
  leafP : Procedure (prodCode trialGlobalsCode nodeInputCode) packedRoundCode
    (fun x => (ops x.1).leaf x.2)
  prepareP : Procedure (prodCode trialGlobalsCode trialCallDataCode) preparedCode
    (fun x => (ops x.1).prepare x.2.1 x.2.2)
  descendP : Procedure (prodCode trialGlobalsCode (prodCode nodeInputCode preparedCode)) nodeInputCode
    (fun x => (ops x.1).childInput x.2.1 x.2.2)
  assembleP : Procedure (prodCode trialGlobalsCode trialCallDataCode) packedRoundCode
    (fun x => (ops x.1).assemble x.2.1 x.2.2)
  finishP : Procedure (prodCode trialGlobalsCode trialFinishDataCode) trialFinishResultCode
    (fun x => (ops x.1).finish x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)

abbrev EnterData := ℕ × NodeInput
abbrev ScheduleData := ℕ × ℕ × NodeInput × List Completed
abbrev FeedbackData := TrialFrame × PackedRound × List Bool
abbrev enterDataCode : EnterData → List Bool := prodCode Nat.bits nodeInputCode
abbrev scheduleDataCode : ScheduleData → List Bool := prodCode Nat.bits (prodCode Nat.bits trialCallDataCode)
abbrev feedbackDataCode : FeedbackData → List Bool := prodCode frameCode (prodCode packedRoundCode id)
abbrev frameFieldsCode := prodCode Nat.bits (prodCode Nat.bits (prodCode nodeInputCode (prodCode trialRowsCode preparedCode)))
abbrev trialTagCode := sumCode (sumCode enterDataCode scheduleDataCode) (sumCode packedRoundCode feedbackDataCode)

def trialTag : TrialPC → (EnterData ⊕ ScheduleData) ⊕ (PackedRound ⊕ FeedbackData)
  | .enter k i => .inl (.inl (k,i))
  | .schedule k n i xs => .inl (.inr (k,n,i,xs))
  | .returned out => .inr (.inl out)
  | .feedback f out tape => .inr (.inr (f,out,tape))

noncomputable def trialTagP : Procedure pcCode trialTagCode trialTag :=
  (identity pcCode).result (by intro c; cases c <;> rfl)

noncomputable def enterPCP : Procedure enterDataCode pcCode (fun x => .enter x.1 x.2) :=
  (prepend enterDataCode [false,false]).result (by intro x; rfl)
noncomputable def schedulePCP : Procedure scheduleDataCode pcCode (fun x => .schedule x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (prepend scheduleDataCode [false,true]).result (by intro x; rfl)
noncomputable def returnPCP : Procedure packedRoundCode pcCode PC.returned :=
  (prepend packedRoundCode [true,false]).result (by intro x; rfl)
noncomputable def feedbackPCP : Procedure feedbackDataCode pcCode (fun x => .feedback x.1 x.2.1 x.2.2) :=
  (prepend feedbackDataCode [true,true]).result (by intro x; rfl)
noncomputable def makeTrialStateP : Procedure (prodCode pcCode trialStackCode) stateCode
    (fun x => ⟨x.1,x.2⟩) :=
  (identity _).result (by intro x; rfl)
noncomputable def makeTrialFrameP : Procedure frameFieldsCode frameCode
    (fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2⟩) :=
  (identity _).result (by intro x; rfl)
def trialFrameFields (f : TrialFrame) := (f.childFuel,f.remaining,f.input,f.prefix,f.prepared)
noncomputable def trialFrameViewP : Procedure frameCode frameFieldsCode trialFrameFields :=
  (identity _).result (by intro x; rfl)

noncomputable def proceedP : Procedure stateCode trialActionCode Action.proceed :=
  (prepend stateCode [false]).result (by intro x; rfl)
noncomputable def askTrialP : Procedure trialResumeCode trialActionCode (fun x => .ask x.1 x.2.1 x.2.2) :=
  (prepend trialResumeCode [true,false]).result (by intro x; rfl)
noncomputable def haltTrialP : Procedure packedRoundCode trialActionCode Action.halt :=
  (prepend packedRoundCode [true,true]).result (by intro x; rfl)

noncomputable def pcOfStateP : Procedure stateCode pcCode State.pc :=
  (first pcCode trialStackCode).precompose (fun s : MachineState => (s.pc,s.stack))
noncomputable def stackOfStateP : Procedure stateCode trialStackCode State.stack :=
  (second pcCode trialStackCode).precompose (fun s : MachineState => (s.pc,s.stack))

/-- A product distributes over a tagged choice using ordinary Boolean tests and
framed pair projections. Defaults are observed exclusively on the unselected branch. -/
noncomputable def choosePacket {A B Z D : Type} {ea : A → List Bool} {eb : B → List Bool}
    {ez : Z → List Bool} {ed : D → List Bool} {f : A × Z → D} {g : B × Z → D}
    (a₀ : A) (b₀ : B) (left : Procedure (prodCode ea ez) ed f)
    (right : Procedure (prodCode eb ez) ed g) :
    Procedure (prodCode (sumCode ea eb) ez) ed
      (fun x => Sum.elim (fun a => f (a,x.2)) (fun b => g (b,x.2)) x.1) := by
  let s := first (sumCode ea eb) ez
  let z := second (sumCode ea eb) ez
  let test := (casesSum (constant ea boolCode true) (constant eb boolCode false)).comp s
  let a := (casesSum (identity ea) (constant eb ea a₀)).comp s
  let b := (casesSum (constant ea eb b₀) (identity eb)).comp s
  apply (conditional test (left.comp (a.pair z)) (right.comp (b.pair z))).congrFun
  rintro ⟨arg,ctx⟩
  cases arg <;> rfl

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
