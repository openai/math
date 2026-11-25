import OAI.Optimization.LinearProgramming.Compression.RequestGraphProbe
import OAI.Optimization.LinearProgramming.Lattice.BitRoundControl

/-! A graph request as a single finite dialogue. Its carry holds the selected
integer coefficients and the existing signed midpoint probe. The result word
contains a flag, the rational slopes, and the rational offset. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable
namespace Dialogue

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit OracleSpec

abbrev Output := Bool × (List ℚ × ℚ)
abbrev Carry := GridArg × Driver.Probe.Carry
abbrev Action := Word ⊕ (Word × Carry)
abbrev Prepared := Bool × GridArg

def outputCode := prodCode boolCode (prodCode ratVectorCode ratCode)
def preparedCode := prodCode boolCode gridArgCode
def carryCode := prodCode gridArgCode Driver.Probe.carryCode
def actionCode := sumCode (id : Word → Word) (prodCode id carryCode)

def failOutput : Output := (false,[],0)
def represent (x : GridArg) (y : ℚ) : Output := (true,slopes x.2,gridOffset x y)

def route (x : GridArg) : Driver.Probe.Action → Action
  | .inl r => .inl (outputCode (represent x (r.2.headD 0)))
  | .inr (row,c) => .inr (Driver.signPacket row,(x,c))

def stage (s : Prepared) : Action :=
  if s.1 then route s.2 (startProbe s.2) else .inl (outputCode failOutput)

def dispatchWith {I : Type} (prepare : I → Prepared) : I ⊕ (Word × Carry) → Action
  | .inl i => stage (prepare i)
  | .inr (answer,x,c) => route x (Driver.Probe.advance (Driver.nonnegativeAnswer answer) c)

noncomputable def routeP : Procedure (prodCode gridArgCode Driver.Probe.actionCode) actionCode
    (fun x => route x.1 x.2) := by
  let e := first gridArgCode Driver.Probe.resultCode
  let r := second gridArgCode Driver.Probe.resultCode
  let vals := (second boolCode Driver.Probe.ratListCode).comp r
  let y := (listHead ratCode (0:ℚ)).comp vals
  let z := (second Nat.bits intRowCode).comp e
  let affine := (constant _ boolCode true).pair ((slopesP.comp z).pair (gridOffsetP.comp (e.pair y)))
  let word : Procedure (prodCode gridArgCode Driver.Probe.resultCode) (id : Word → Word)
      (fun s => outputCode (represent s.1 (s.2.2.headD 0))) := affine.result (fun _ => rfl)
  let done := Driver.Probe.leftP (prodCode (id : Word → Word) carryCode) word
  let qs := prodCode intRowCode Driver.Probe.carryCode
  let x := first gridArgCode qs
  let pair := second gridArgCode qs
  let row := (first intRowCode Driver.Probe.carryCode).comp pair
  let c := (second intRowCode Driver.Probe.carryCode).comp pair
  let ask := Driver.Probe.rightP (id : Word → Word) ((Driver.signPacketP.comp row).pair (x.pair c))
  refine (Driver.casesWithP ((false,[]):Driver.Probe.Result) (([],default):List ℤ × Driver.Probe.Carry)
    done ask).congrFun ?_
  rintro ⟨g,a⟩
  cases a <;> rfl

noncomputable def stageP : Procedure preparedCode actionCode stage := by
  let flag := first boolCode gridArgCode
  let arg := second boolCode gridArgCode
  let run := routeP.comp (arg.pair (startProbeP.comp arg))
  let reject := constant preparedCode actionCode (.inl (outputCode failOutput) : Action)
  exact conditional flag run reject

noncomputable def dispatchWithP {I : Type} {ei : I → Word} {prepare : I → Prepared}
    (p : Procedure ei preparedCode prepare) : WordDialogue.ProcedureOf ei carryCode (dispatchWith prepare) := by
  let wc := prodCode (id : Word → Word) carryCode
  let answer := first (id : Word → Word) carryCode
  let carry := second (id : Word → Word) carryCode
  let x := (first gridArgCode Driver.Probe.carryCode).comp carry
  let k := (second gridArgCode Driver.Probe.carryCode).comp carry
  let advance := conditional (Driver.nonnegativeAnswerP.comp answer)
    ((Driver.Probe.advanceP true).comp k) ((Driver.Probe.advanceP false).comp k)
  let reply := routeP.comp (x.pair advance)
  have core : Procedure (sumCode ei wc) actionCode (dispatchWith prepare) := by
    refine (casesSum (stageP.comp p) reply).congrFun ?_
    rintro (i|⟨w,x,k⟩)
    · rfl
    · cases h : Driver.nonnegativeAnswer w <;> simp [dispatchWith,h,Function.comp_def]
  refine core.congrEncoding ?_ ?_
  · rintro (i|⟨w,c⟩)
    · rfl
    · simp [wc,WordDialogue.stateCode,sumCode,prodCode,pairBits,quoteBits_eq_frame]
  · rintro (w|⟨w,c⟩)
    · rfl
    · simp [actionCode,WordDialogue.actionCode,sumCode,prodCode,pairBits,quoteBits_eq_frame]

end Dialogue
end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
