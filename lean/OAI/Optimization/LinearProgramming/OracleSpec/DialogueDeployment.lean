import OAI.Optimization.LinearProgramming.OracleSpec.DialogueProof

/-! Deploy a finite pure stack `Procedure` as the dispatcher of an interactive machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace Dialogue

variable {I C : Type}

open ExactQuantumFactoring.BitStackProgram
open BitCode

/-- Reserve three fresh registers outside the dispatcher's entire working storage. -/
def publicPorts {K : Type} (wire : K) : Fin 4 ↪ (K ⊕ Fin 3) where
  toFun := Fin.cases (.inl wire) Sum.inr
  inj' := by
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp

section Deployment
variable {ei : I → Word} {ec : C → Word} {dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)}

abbrev ProcedureOf (ei : I → Word) (ec : C → Word) (dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)) :=
  Procedure (inputCode ei ec) (actionCode ec) dispatch

noncomputable def layout (p : ProcedureOf ei ec dispatch) : Ports (Fintype.card (p.shared.K ⊕ Fin 3)) :=
  ⟨(publicPorts p.shared.input).trans (Fintype.equivFin _).toEmbedding⟩

noncomputable def registers (p : ProcedureOf ei ec dispatch) : p.shared.K ↪ Fin (Fintype.card (p.shared.K ⊕ Fin 3)) :=
  (leftEmbed _ (Fin 3)).trans (Fintype.equivFin _).toEmbedding

noncomputable def stepCode (p : ProcedureOf ei ec dispatch) : BitCode (Fintype.card (p.shared.K ⊕ Fin 3)) :=
  ofBitStack (p.shared.program.relabel (registers p))

/-- One physical, input-independent finite-control machine implements all interaction lengths. -/
noncomputable def machine (p : ProcedureOf ei ec dispatch) : BitProgram :=
  ((layout p).code (stepCode p)).compile (layout p).wire (layout p).io

/-- The pure kernel leaves only its single public wire occupied between successive rounds. -/
theorem dispatch_exec (p : ProcedureOf ei ec dispatch) (reply : Transcript → Word → Bool) (L : ℕ) :
    ∀ s h, (inputCode ei ec s).length ≤ L → ∃ n ≤ p.shared.bound.eval L,
      Executes (layout p).io (fun past q => [reply past q]) (stepCode p)
        ((layout p).mem (inputCode ei ec s) [] [] [] h)
        ((layout p).mem (actionCode ec (dispatch s)) [] [] [] h) n := by
  classical
  intro s h hlen
  obtain ⟨n, hn, run⟩ := procedure_exec p.shared (registers p) (fun _ => []) (layout p).io
    (fun past q => [reply past q]) [] h s
  refine ⟨n, hn.trans (Procedure.eval_nat_mono _ hlen), ?_⟩
  rw [overlay_singleton, overlay_singleton] at run
  have wire : (layout p).wire = (registers p) p.shared.input := rfl
  simpa only [stepCode, Ports.mem, Ports.store_singleton, wire] using run

/-- Kernel-checked dispatcher cost plus serialization, replies, loop tests, and final output.
The polynomial `P` is `p.shared.bound` and `L` bounds the sizes of actual states and requests in this session. -/
theorem machine_computes (p : ProcedureOf ei ec dispatch) (reply : Transcript → Word → Bool)
    {L x v history rounds} (hs : Session ei ec dispatch reply L (.inl x) [] v history rounds) :
    (machine p).ComputesWithin (fun past q => [reply past q]) (ei x)
      (rounds * (p.shared.bound.eval L + 10*L + 15) + 3) (fun hist bits => hist = history ∧ bits = [v]) := by
  exact (layout p).computes (stepCode p) ei ec dispatch reply L (p.shared.bound.eval L)
    (dispatch_exec p reply L) hs

end Deployment
end Dialogue
end OracleSpec
end LinearProgramming
end Optimization
end OAI
