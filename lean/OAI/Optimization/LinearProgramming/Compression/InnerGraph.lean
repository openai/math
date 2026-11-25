import OAI.Optimization.LinearProgramming.Compression.InnerVectors
import OAI.Optimization.LinearProgramming.Compression.RequestGraphNative

/-! The graph subprogram already returns its typed slopes, offset and success bit on a
self-delimiting wire. The larger controller consumes that exact format in place. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Graph
open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

abbrev Out := RequestTable.Dialogue.Output
abbrev Carry := RequestTable.Dialogue.Carry
abbrev Action := Out ⊕ (Word × Carry)

def actionCode := sumCode RequestTable.Dialogue.outputCode (prodCode (id : Word → Word) RequestTable.Dialogue.carryCode)

def wire : Action → RequestTable.Dialogue.Action
  | .inl v => .inl (RequestTable.Dialogue.outputCode v)
  | .inr q => .inr q

def route (x : RequestTable.GridArg) : Driver.Probe.Action → Action
  | .inl r => .inl (RequestTable.Dialogue.represent x (r.2.headD 0))
  | .inr (a,c) => .inr (Driver.signPacket a,(x,c))

noncomputable def dispatch : RequestTable.Input ⊕ (Word × Carry) → Action
  | .inl input =>
    let prep := RequestTable.prepare input
    if prep.1 then route prep.2 (RequestTable.startProbe prep.2) else .inl RequestTable.Dialogue.failOutput
  | .inr (w,x,c) => route x (Driver.Probe.advance (Driver.nonnegativeAnswer w) c)

private theorem wire_route (x : RequestTable.GridArg) (a : Driver.Probe.Action) :
    wire (route x a)=RequestTable.Dialogue.route x a := by rcases a with r|⟨row,c⟩ <;> rfl

theorem wire_dispatch (s : RequestTable.Input ⊕ (Word × Carry)) :
    wire (dispatch s) = RequestTable.graphRequestDispatch s := by
  rcases s with x|⟨w,x,c⟩
  · simp only [dispatch,RequestTable.graphRequestDispatch,RequestTable.Dialogue.dispatchWith,RequestTable.Dialogue.stage]
    split
    · exact wire_route _ _
    · rfl
  · exact wire_route _ _

/-- Reuse the complete native packed graph dispatcher with its unchanged binary program. -/
noncomputable def dispatchP :
    Procedure (WordDialogue.stateCode RequestTable.inputCode RequestTable.Dialogue.carryCode) actionCode dispatch :=
  RequestTable.graphRequestDispatchP.result (by
    intro s
    rw [← wire_dispatch]
    cases dispatch s with
    | inl r => rfl
    | inr q => simp [wire,actionCode,sumCode,WordDialogue.actionCode,prodCode,pairBits,quoteBits_eq_frame])

end Graph
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
