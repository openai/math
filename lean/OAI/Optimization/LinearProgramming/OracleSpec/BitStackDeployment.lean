import OAI.Optimization.LinearProgramming.OracleSpec.BitStack

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace BitCode

variable {k : ℕ}

open ExactQuantumFactoring.BitStackProgram

private theorem overlay_equiv_singleton {K : Type} [DecidableEq K] (e : K ≃ Fin k) (j : K) (v : Word) :
    overlay e.toEmbedding (fun _ => []) (singletonStore j v) = singletonStore (e j) v := by
  funext i
  obtain ⟨i, rfl⟩ := e.surjective i
  rw [show overlay e.toEmbedding (fun _ => []) (singletonStore j v) (e i) =
    singletonStore j v i from overlay_at e.toEmbedding _ _ i]
  by_cases h : i = j
  · subst i; simp [singletonStore]
  · have h' : e i ≠ e j := fun h' => h (e.injective h')
    simp [singletonStore, h, h']

private theorem singleton_initial (i : Fin k) (v : Word) :
    (⟨singletonStore i v, [], []⟩ : Memory k) = startMemory i v := by
  simp only [startMemory, Memory.mk.injEq, and_true]
  funext j
  by_cases h : j = i <;> simp [singletonStore, h]

/-- A fixed, finite program in the comparator's bit-machine model for each existing
polynomial-time procedure. The register reindexing depends only on the finite program. -/
noncomputable def deploy {α β : Type} {ea : α → Word} {eb : β → Word} {f : α → β}
    (proc : Procedure ea eb f) : BitProgram :=
  let e := Fintype.equivFin proc.K
  ((ofBitStack (proc.program.relabel e)).seq (drain (e proc.output))).compile (e proc.input) (e proc.input)

/-- Includes the final serialization and halt. The output is produced by the instruction
trace, under any oracle (there are no queries in this subroutine). -/
theorem deploy_correct {α β : Type} {ea : α → Word} {eb : β → Word} {f : α → β}
    (proc : Procedure ea eb f) (o : WordOracle) (x : α) :
    (deploy proc).ComputesWithin o (ea x) (3 * proc.bound.eval (ea x).length + 2 * (ea x).length + 2)
      (fun history bits => history = [] ∧ bits = eb (f x)) := by
  classical
  let e := Fintype.equivFin proc.K
  let a := e proc.input
  let b := e proc.output
  let result : Memory _ := ⟨singletonStore b (eb (f x)), [], []⟩
  obtain ⟨n, hn, run⟩ := procedure_exec proc e.toEmbedding (fun _ => []) a o [] [] x
  rw [overlay_equiv_singleton, overlay_equiv_singleton, singleton_initial] at run
  have hd : result.store b = eb (f x) := by simp [result, singletonStore]
  have write := drain_exec b a o result
  rw [hd] at write
  apply compile_computes (m := result.drained b) (n := n + (2 * (eb (f x)).length + 1))
  · exact Executes.seq run write
  · have hlen := proc.output_length_le x
    omega
  · simp [Memory.drained, result, singletonStore]

end BitCode
end OracleSpec
end LinearProgramming
end Optimization
end OAI
