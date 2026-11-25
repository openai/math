import OAI.Optimization.LinearProgramming.Lattice.BitProbeRatios
import OAI.Optimization.LinearProgramming.Lattice.BitRoundCodes
import OAI.Optimization.LinearProgramming.OracleSpec.WordDialogueDeployment

/-! One adaptive transition table for every ambient dimension and every binary radius.
Each outgoing request carries the exact signed row, and the persistent continuation
contains only its row history and the state of one current residual probe. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open OracleSpec

structure KernelCode (f : Kernels) where
  projection : Procedure (prodCode unaryCode intMatrixCode) intMatrixCode f.projection
  selector : Procedure (prodCode Nat.bits Probe.ratListCode) (prodCode Nat.bits intRowCode) f.selector
  assemble : Procedure (prodCode (prodCode unaryCode unaryCode) intMatrixCode) intRowCode f.assemble

variable {A B C D : Type} {ea : A → Word} {eb : B → Word} {ec : C → Word} {ed : D → Word}

/-- Case analysis with ordinary local context retained on both branches. -/
noncomputable def casesWithP (b₀ : B) (c₀ : C) {f : A × B → D} {g : A × C → D}
    (p : Procedure (prodCode ea eb) ed f) (q : Procedure (prodCode ea ec) ed g) :
    Procedure (prodCode ea (sumCode eb ec)) ed (fun x : A × (B ⊕ C) =>
      (x.2.elim (fun b => f (x.1,b)) (fun c => g (x.1,c)))) := by
  let a := first ea (sumCode eb ec)
  let choice := second ea (sumCode eb ec)
  let b := (casesSum (identity eb) (constant ec eb b₀)).comp choice
  let c := (casesSum (constant eb ec c₀) (identity ec)).comp choice
  let tag := (head.precompose (sumCode eb ec)).comp choice
  refine (conditional tag (q.comp (a.pair c)) (p.comp (a.pair b))).congrFun ?_
  rintro ⟨x,y⟩
  cases y <;> rfl

noncomputable def finishP {f : Kernels} (p : KernelCode f) : Procedure envCode actionCode (finish f) := by
  let base := first (prodCode inputCode unaryCode) intMatrixCode
  let input := (first inputCode unaryCode).comp base
  let dim := (first unaryCode Nat.bits).comp input
  let width := radixWidthP.comp input
  let old := second (prodCode inputCode unaryCode) intMatrixCode
  exact Probe.leftP (prodCode id carryCode) (signPacketP.comp (p.assemble.comp ((dim.pair width).pair old)))

noncomputable def forwardP : Procedure (prodCode envCode (prodCode intRowCode Probe.carryCode))
    actionCode (fun x => forward x.1 x.2) := by
  let e := first envCode (prodCode intRowCode Probe.carryCode)
  let q := second envCode (prodCode intRowCode Probe.carryCode)
  let row := (first intRowCode Probe.carryCode).comp q
  let carry := (second intRowCode Probe.carryCode).comp q
  exact Probe.rightP (id : Word → Word) ((signPacketP.comp row).pair (e.pair carry))

noncomputable def probeParamsP {f : Kernels} (p : KernelCode f) :
    Procedure envCode Probe.paramsCode (probeParams f) := by
  let base := first (prodCode inputCode unaryCode) intMatrixCode
  let input := (first inputCode unaryCode).comp base
  let dim := (first unaryCode Nat.bits).comp input
  let old := second (prodCode inputCode unaryCode) intMatrixCode
  exact (dim.pair (searchPrecisionP.comp input)).pair (p.projection.comp (dim.pair old))

noncomputable def requestOfP : Procedure Probe.actionCode (prodCode intRowCode Probe.carryCode) requestOf :=
  (casesSum (constant Probe.resultCode (prodCode intRowCode Probe.carryCode) ([],default))
    (identity (prodCode intRowCode Probe.carryCode))).congrFun (by rintro (x|y) <;> rfl)

noncomputable def stageP {f : Kernels} (p : KernelCode f) : Procedure envCode actionCode (stage f) := by
  let base := first (prodCode inputCode unaryCode) intMatrixCode
  let fuel := (second inputCode unaryCode).comp base
  let question := requestOfP.comp (Probe.startP.comp (probeParamsP p))
  let active := forwardP.comp ((identity envCode).pair question)
  refine (conditional (Probe.zeroUnaryP.comp fuel) (finishP p) active).congrFun ?_
  intro e
  by_cases h : e.1.2 = 0 <;> simp [stage,h,Function.comp_def]

noncomputable def receiveProbeP {f : Kernels} (p : KernelCode f) :
    Procedure (prodCode envCode Probe.actionCode) actionCode (fun x => receiveProbe f x.1 x.2) := by
  let e := first envCode Probe.resultCode
  let reply := second envCode Probe.resultCode
  let flag := (first boolCode Probe.ratListCode).comp reply
  let vals := (second boolCode Probe.ratListCode).comp reply
  let base := (first (prodCode inputCode unaryCode) intMatrixCode).comp e
  let input := (first inputCode unaryCode).comp base
  let fuel := (second inputCode unaryCode).comp base
  let radius := (second unaryCode Nat.bits).comp input
  let old := (second (prodCode inputCode unaryCode) intMatrixCode).comp e
  let digit := (second Nat.bits intRowCode).comp (p.selector.comp (radius.pair vals))
  let updated := (input.pair (unaryPred.comp fuel)).pair ((listCons (ea:=intRowCode)).comp (digit.pair old))
  let finished := conditional flag ((stageP p).comp updated) ((finishP p).comp e)
  refine (casesWithP ((false,[]):Probe.Result) (([],default):Row×Probe.Carry) finished forwardP).congrFun ?_
  rintro ⟨e,a⟩
  rcases a with ⟨b,xs⟩ | q
  · cases b <;> rfl
  · rfl

def rawDispatchCode := sumCode inputCode (prodCode (id : Word → Word) carryCode)

noncomputable def dispatchP {f : Kernels} (p : KernelCode f) :
    WordDialogue.ProcedureOf inputCode carryCode (dispatch f) := by
  let d := first unaryCode Nat.bits
  let initial := ((identity inputCode).pair d).pair (constant inputCode intMatrixCode ([]:IntMatrix))
  let start := (stageP p).comp initial
  let w := first (id : Word → Word) carryCode
  let carry := second (id : Word → Word) carryCode
  let e := (first envCode Probe.carryCode).comp carry
  let k := (second envCode Probe.carryCode).comp carry
  let probe := conditional (nonnegativeAnswerP.comp w) ((Probe.advanceP true).comp k) ((Probe.advanceP false).comp k)
  let res := (receiveProbeP p).comp (e.pair probe)
  have core : Procedure rawDispatchCode actionCode (dispatch f) := by
    refine (casesSum start res).congrFun ?_
    rintro (x|⟨w,e,k⟩)
    · rfl
    · cases h : nonnegativeAnswer w <;> simp [dispatch,h,Function.comp_def]
  have hInput : WordDialogue.stateCode inputCode carryCode = rawDispatchCode := by
    funext x
    rcases x with x | ⟨w,c⟩
    · rfl
    · simp [WordDialogue.stateCode,rawDispatchCode,sumCode,prodCode,pairBits,quoteBits_eq_frame]
  have hOutput : WordDialogue.actionCode carryCode = actionCode := by
    funext x
    rcases x with x | ⟨w,c⟩
    · rfl
    · simp [WordDialogue.actionCode,actionCode,sumCode,prodCode,pairBits,quoteBits_eq_frame]
  unfold WordDialogue.ProcedureOf
  rw [hInput,hOutput]
  exact core

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
