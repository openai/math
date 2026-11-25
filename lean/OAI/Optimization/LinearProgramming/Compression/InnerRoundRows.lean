import OAI.Optimization.LinearProgramming.Lattice.BitRoundControl

/-! The native rounding controller before its final serialization of a signed row. Both
the query and the return row can be used by a surrounding finite pure controller. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Round

open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

abbrev Row := List ℤ
abbrev Action := Row ⊕ (Row × Driver.Carry)
def actionCode : Action → Word := sumCode intRowCode (prodCode intRowCode Driver.carryCode)

def wire : Action → Driver.Action
  | .inl z => .inl (Driver.signPacket z)
  | .inr (a,c) => .inr (Driver.signPacket a,c)

def finish (f : Driver.Kernels) (e : Driver.Env) : Action :=
  .inl (f.assemble ((e.1.1.1,Lattice.radixWidth e.1.1.1 e.1.1.2),e.2))

def forward (e : Driver.Env) (q : Row × Driver.Probe.Carry) : Action := .inr (q.1,e,q.2)

def stage (f : Driver.Kernels) (e : Driver.Env) : Action :=
  if e.1.2=0 then finish f e else forward e (Driver.requestOf (Driver.Probe.start (Driver.probeParams f e)))

def receive (f : Driver.Kernels) (e : Driver.Env) : Driver.Probe.Action → Action
  | .inr q => forward e q
  | .inl (nz,vs) => if nz then stage f ((e.1.1,e.1.2-1),(f.selector (e.1.1.2,vs)).2::e.2) else finish f e

def dispatch (f : Driver.Kernels) : Driver.Input ⊕ (Word × Driver.Carry) → Action
  | .inl x => stage f ((x,x.1),[])
  | .inr (w,e,c) => receive f e (Driver.Probe.advance (Driver.nonnegativeAnswer w) c)

@[simp] theorem wire_stage (f : Driver.Kernels) (e : Driver.Env) : wire (stage f e)=Driver.stage f e := by
  unfold stage Driver.stage
  split <;> rfl

@[simp] theorem wire_receive (f : Driver.Kernels) (e : Driver.Env) (a : Driver.Probe.Action) :
    wire (receive f e a)=Driver.receiveProbe f e a := by
  rcases a with ⟨b,xs⟩|q
  · cases b with
    | false => rfl
    | true => exact wire_stage _ _
  · rfl

/-- Erasing the row view by the official signed packet format recovers the exact original dispatcher. -/
theorem wire_dispatch (f : Driver.Kernels) (x : Driver.Input ⊕ (Word × Driver.Carry)) :
    wire (dispatch f x)=Driver.dispatch f x := by
  rcases x with x|⟨w,e,c⟩ <;> simp [dispatch,Driver.dispatch]

noncomputable def finishP {f : Driver.Kernels} (p : Driver.KernelCode f) :
    Procedure Driver.envCode actionCode (finish f) := by
  let base := first (prodCode Driver.inputCode unaryCode) intMatrixCode
  let input := (first Driver.inputCode unaryCode).comp base
  let dim := (first unaryCode Nat.bits).comp input
  let w := Driver.radixWidthP.comp input
  let old := second (prodCode Driver.inputCode unaryCode) intMatrixCode
  exact Driver.Probe.leftP (prodCode intRowCode Driver.carryCode) (p.assemble.comp ((dim.pair w).pair old))

noncomputable def forwardP : Procedure (prodCode Driver.envCode (prodCode intRowCode Driver.Probe.carryCode))
    actionCode (fun x => forward x.1 x.2) := by
  let e := first Driver.envCode (prodCode intRowCode Driver.Probe.carryCode)
  let pair := second Driver.envCode (prodCode intRowCode Driver.Probe.carryCode)
  let row := (first intRowCode Driver.Probe.carryCode).comp pair
  let c := (second intRowCode Driver.Probe.carryCode).comp pair
  exact Driver.Probe.rightP intRowCode (row.pair (e.pair c))

noncomputable def stageP {f : Driver.Kernels} (p : Driver.KernelCode f) :
    Procedure Driver.envCode actionCode (stage f) := by
  let base := first (prodCode Driver.inputCode unaryCode) intMatrixCode
  let fuel := (second Driver.inputCode unaryCode).comp base
  let ask := Driver.requestOfP.comp (Driver.Probe.startP.comp (Driver.probeParamsP p))
  let active := forwardP.comp ((identity Driver.envCode).pair ask)
  refine (conditional (Driver.Probe.zeroUnaryP.comp fuel) (finishP p) active).congrFun ?_
  intro e; by_cases h : e.1.2=0 <;> simp [stage,h,Function.comp_def]

noncomputable def receiveP {f : Driver.Kernels} (p : Driver.KernelCode f) :
    Procedure (prodCode Driver.envCode Driver.Probe.actionCode) actionCode (fun x => receive f x.1 x.2) := by
  let e := first Driver.envCode Driver.Probe.resultCode
  let reply := second Driver.envCode Driver.Probe.resultCode
  let flag := (first boolCode Driver.Probe.ratListCode).comp reply
  let vals := (second boolCode Driver.Probe.ratListCode).comp reply
  let base := (first (prodCode Driver.inputCode unaryCode) intMatrixCode).comp e
  let input := (first Driver.inputCode unaryCode).comp base
  let fuel := (second Driver.inputCode unaryCode).comp base
  let radius := (second unaryCode Nat.bits).comp input
  let old := (second (prodCode Driver.inputCode unaryCode) intMatrixCode).comp e
  let digit := (second Nat.bits intRowCode).comp (p.selector.comp (radius.pair vals))
  let updated := (input.pair (unaryPred.comp fuel)).pair ((listCons (ea := intRowCode)).comp (digit.pair old))
  let done := conditional flag ((stageP p).comp updated) ((finishP p).comp e)
  refine (Driver.casesWithP ((false,[]):Driver.Probe.Result) (([],default):Row×Driver.Probe.Carry) done forwardP).congrFun ?_
  rintro ⟨e,a⟩
  rcases a with ⟨b,xs⟩|q
  · cases b <;> rfl
  · rfl

/-- Fixed transition program using each native projection, LLL selector and radix routine. -/
noncomputable def dispatchP {f : Driver.Kernels} (p : Driver.KernelCode f) :
    Procedure Driver.rawDispatchCode actionCode (dispatch f) := by
  let dim := first unaryCode Nat.bits
  let start := (stageP p).comp (((identity Driver.inputCode).pair dim).pair (constant Driver.inputCode intMatrixCode ([]:IntMatrix)))
  let w := first (id : Word → Word) Driver.carryCode
  let carry := second (id : Word → Word) Driver.carryCode
  let e := (first Driver.envCode Driver.Probe.carryCode).comp carry
  let k := (second Driver.envCode Driver.Probe.carryCode).comp carry
  let probe := conditional (Driver.nonnegativeAnswerP.comp w) ((Driver.Probe.advanceP true).comp k) ((Driver.Probe.advanceP false).comp k)
  let res := (receiveP p).comp (e.pair probe)
  refine (casesSum start res).congrFun ?_
  rintro (x|⟨w,e,k⟩)
  · rfl
  · cases h : Driver.nonnegativeAnswer w <;> simp [dispatch,h,Function.comp_def]

end Round
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
