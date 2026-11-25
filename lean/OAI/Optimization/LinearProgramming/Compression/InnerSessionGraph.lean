import OAI.Optimization.LinearProgramming.Compression.InnerSessionSizes
import OAI.Optimization.LinearProgramming.Compression.InnerPackets

/-! The exact tagged graph output is substituted directly into the caller's affine dot
product without manufacturing an external oracle answer between the two steps. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

/-- Run the graph phase from any physical dispatch boundary having the specified first action. -/
theorem liftGraph (o : WordOracle) (past : Transcript) (L B : ℕ) (gamma : Rats)
    (v : Graph.Out) (st : RequestTable.Input ⊕ (Word × Graph.Carry)) (hist : Transcript) (k : ℕ)
    (sub : WordDialogue.Session RequestTable.inputCode RequestTable.Dialogue.carryCode
      RequestTable.graphRequestDispatch (oracleWith past id o) L st [] (RequestTable.Dialogue.outputCode v) hist k)
    (hcarry : L+2*(Projector.rowCode gamma).length+4 ≤ B) (hout : (outputWord (affineResult gamma v)).length≤B)
    (outerSt : Input ⊕ (Word × Carry)) (hstart : dispatch outerSt=routeGraph gamma (Graph.dispatch st))
    (hsize : (WordDialogue.stateCode inputEncoding carryCode outerSt).length≤B) :
    ∃ final cnt, cnt≤k+1 ∧ WordDialogue.Session inputEncoding carryCode dispatch o B outerSt past
      (outputWord (affineResult gamma v)) final cnt ∧ final=hist++past := by
  let done (u : Graph.Out) : Action := .inl (outputWord (affineResult gamma u))
  let embed (c : Graph.Carry) : Carry := .inr (.inr (gamma,c))
  have erases (a : Graph.Action) : wireView RequestTable.Dialogue.outputCode id a = Graph.wire a := by
    rcases a with u | ⟨packet,c⟩ <;> rfl
  have routes (a : Graph.Action) : routeGraph gamma a = routeView done id embed a := by
    rcases a with u | ⟨packet,c⟩ <;> rfl
  have result := transferSession (ei := RequestTable.inputCode) (ec := RequestTable.Dialogue.carryCode)
    (ej := inputEncoding) (ek := carryCode) (sub := RequestTable.graphRequestDispatch) (outer := dispatch)
    Graph.dispatch RequestTable.Dialogue.outputCode id
    (fun s => (erases _).trans (Graph.wire_dispatch s)) done id embed id (fun _ => rfl)
    (fun w c => routes (Graph.dispatch (.inr (w,c)))) past o (fun h => h=hist++past) L B 1 (by omega)
    (fun _ h => h.trans (by omega))
    (fun w c h => (graphCarry_size gamma w c).trans (by omega)) sub (by
      intro y hy s hstep hlen
      have eq : y=v := graphOutputCode_injective hy
      subst y
      let h := historyWith past id hist
      exact ⟨h,1,by decide,WordDialogue.Session.done hstep hlen hout,by simp [h,historyWith]⟩)
    outerSt (hstart.trans (routes _)) hsize
  simpa [historyWith] using result

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
