import OAI.Optimization.LinearProgramming.OracleSpec.WordDialogue
import OAI.Optimization.LinearProgramming.OracleSpec.DialogueDeployment

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace WordDialogue

variable {I C : Type}

open ExactQuantumFactoring.BitStackProgram BitCode
open Dialogue (Ports)

variable {ei : I → Word} {ec : C → Word} {dispatch : I ⊕ (Word × C) → Word ⊕ (Word × C)}

abbrev ProcedureOf (ei : I → Word) (ec : C → Word)
    (dispatch : I ⊕ (Word × C) → Word ⊕ (Word × C)) :=
  Procedure (stateCode ei ec) (actionCode ec) dispatch

noncomputable def layout (p : ProcedureOf ei ec dispatch) : Ports (Fintype.card (p.shared.K ⊕ Fin 3)) :=
  ⟨(Dialogue.publicPorts p.shared.input).trans (Fintype.equivFin _).toEmbedding⟩

noncomputable def registers (p : ProcedureOf ei ec dispatch) : p.shared.K ↪ Fin (Fintype.card (p.shared.K ⊕ Fin 3)) :=
  (leftEmbed _ (Fin 3)).trans (Fintype.equivFin _).toEmbedding

noncomputable def stepCode (p : ProcedureOf ei ec dispatch) : BitCode (Fintype.card (p.shared.K ⊕ Fin 3)) :=
  ofBitStack (p.shared.program.relabel (registers p))

noncomputable def machine (p : ProcedureOf ei ec dispatch) : BitProgram :=
  (code (layout p) (stepCode p)).compile (layout p).wire (layout p).io

theorem dispatch_exec (p : ProcedureOf ei ec dispatch) (o : WordOracle) (L : ℕ) :
    ∀ s h, (stateCode ei ec s).length ≤ L → ∃ n ≤ p.shared.bound.eval L,
      Executes (layout p).io o (stepCode p) ((layout p).mem (stateCode ei ec s) [] [] [] h)
        ((layout p).mem (actionCode ec (dispatch s)) [] [] [] h) n := by
  classical
  intro s h hlen
  obtain ⟨n,hn,run⟩ := procedure_exec p.shared (registers p) (fun _ => []) (layout p).io o [] h s
  refine ⟨n,hn.trans (Procedure.eval_nat_mono _ hlen),?_⟩
  rw [overlay_singleton,overlay_singleton] at run
  have wire : (layout p).wire = (registers p) p.shared.input := rfl
  simpa only [stepCode,Ports.mem,Ports.store_singleton,wire] using run

/-- The fixed table runs any verified finite word dialogue. The entire output is present on
the result wire, and the concrete transcript coincides with the specified exchange history. -/
theorem machine_computes (p : ProcedureOf ei ec dispatch) (o : WordOracle)
    {L x v history rounds} (hs : Session ei ec dispatch o L (.inl x) [] v history rounds) :
    (machine p).ComputesWithin o (ei x) (rounds * (p.shared.bound.eval L + 18*L+18)+3)
      (fun hist bits => hist = history ∧ bits = v) :=
  computes (layout p) (stepCode p) ei ec dispatch o L (p.shared.bound.eval L) (dispatch_exec p o L) hs

end WordDialogue
end OracleSpec
end LinearProgramming
end Optimization
end OAI
