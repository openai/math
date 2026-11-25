import OAI.Optimization.LinearProgramming.OracleSpec.DialogueDeployment
import OAI.Optimization.LinearProgramming.OracleSpec.UnaryBootstrap

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace Dialogue

variable {I C : Type}
open ExactQuantumFactoring.BitStackProgram
open BitCode

/-- The same finite controller after a dimension-dependent, explicitly charged input initializer. -/
noncomputable def paddedMachine {ei : I → Word} {ec : C → Word}
    {dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)} (p : ProcedureOf ei ec dispatch) : BitProgram :=
  let d := layout p
  ((ofBitStack (UnaryBootstrap.program.relabel d.slot)).seq (d.code (stepCode p))).compile d.wire d.io

/-- The public input is the original binary word, while `p` may use the value of N in a
word-length-polynomial bound because the machine builds its own unary dimension prefix. -/
theorem paddedMachine_computes {ei : I → Word} {ec : C → Word}
    {dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)} (p : ProcedureOf ei ec dispatch)
    (reply : Transcript → Word → Bool) (n : ℕ) (rest : Word) {x : I}
    (pad : ei x = frame (List.replicate n true) ++ (encodeNat n ++ rest))
    {L v history rounds} (hs : Session ei ec dispatch reply L (.inl x) [] v history rounds) :
    (paddedMachine p).ComputesWithin (fun past q => [reply past q]) (encodeNat n ++ rest)
      (64*(n+1)^2 + rounds*(p.shared.bound.eval L+10*L+15)+3)
      (fun hist bits => hist = history ∧ bits = [v]) := by
  let d := layout p
  let o : WordOracle := fun past q => [reply past q]
  obtain ⟨b,hb,hpre⟩ := UnaryBootstrap.program_runs n rest
  have boots := ofBitStack_exec (hpre.relabel d.slot (fun _ => [])) d.io o [] []
  rw [overlay_singleton, overlay_singleton, ← pad] at boots
  have initialized : Executes d.io o (ofBitStack (UnaryBootstrap.program.relabel d.slot))
      (startMemory d.wire (encodeNat n ++ rest)) (startMemory d.wire (ei x)) b := by
    simpa only [d.source_start, Ports.mem, Ports.store_singleton] using boots
  obtain ⟨u, hu, loopRun⟩ := d.code_exec (stepCode p) ei ec dispatch reply L (p.shared.bound.eval L)
    (dispatch_exec p reply L) hs
  apply compile_computes (Executes.seq initialized loopRun) (by omega)
  exact ⟨rfl, rfl⟩

end Dialogue
end OracleSpec
end LinearProgramming
end Optimization
end OAI
