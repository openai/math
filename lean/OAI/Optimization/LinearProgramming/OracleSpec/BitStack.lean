import OAI.Optimization.LinearProgramming.OracleSpec.CompilerIO
import OAI.Computability.QuantumFactoring.BitStackProcedures
import OAI.Computability.QuantumFactoring.BitStackRelabel

/-! Existing finite Boolean-stack procedures run as internal subroutines of the oracle machine.
This preserves their proved execution costs and leaves the oracle transcript untouched. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace BitCode

variable {k : ℕ}

open ExactQuantumFactoring.BitStackProgram

/-- Literal embedding of the sibling package's public bit-stack language. -/
def ofBitStack : Program (Fin k) → BitCode k
  | .skip => .skip
  | .push s b => .push s b
  | .seq p q => .seq (ofBitStack p) (ofBitStack q)
  | .cases s p q r => .cases s (ofBitStack p) (ofBitStack q) (ofBitStack r)
  | .loop s p q => .loop s (ofBitStack p) (ofBitStack q)

theorem ofBitStack_exec {p : Program (Fin k)} {s t : Store (Fin k)} {steps : ℕ}
    (h : Runs p s t steps) (a : Fin k) (o : WordOracle) (buf : Word) (hist : Transcript) :
    Executes a o (ofBitStack p) ⟨s, buf, hist⟩ ⟨t, buf, hist⟩ steps := by
  induction h with
  | skip s => exact .skip _
  | push s k b => exact .push _ _ _
  | seq _ _ ihp ihq => simpa only [ofBitStack, Nat.add_comm] using Executes.seq ihp ihq
  | @cases_nil j p q r s t c hs _ ih =>
    simpa only [ofBitStack, Nat.add_comm] using Executes.casesNil (s := j) (q := ofBitStack q)
      (r := ofBitStack r) hs ih
  | @cases_false j p q r s t xs c hs _ ih =>
    have hpop : (Memory.pop ⟨s,buf,hist⟩ j) = ⟨Function.update s j xs,buf,hist⟩ := by
      simp [Memory.pop, hs]
    have body : Executes a o (ofBitStack q) (Memory.pop ⟨s,buf,hist⟩ j) ⟨t,buf,hist⟩ c :=
      hpop ▸ ih
    simpa only [ofBitStack, Nat.add_comm] using Executes.casesFalse (p := ofBitStack p) (r := ofBitStack r) hs body
  | @cases_true j p q r s t xs c hs _ ih =>
    have hpop : (Memory.pop ⟨s,buf,hist⟩ j) = ⟨Function.update s j xs,buf,hist⟩ := by
      simp [Memory.pop, hs]
    have body : Executes a o (ofBitStack r) (Memory.pop ⟨s,buf,hist⟩ j) ⟨t,buf,hist⟩ c :=
      hpop ▸ ih
    simpa only [ofBitStack, Nat.add_comm] using Executes.casesTrue (p := ofBitStack p) (q := ofBitStack q) hs body
  | @loop_nil j p q s hs => exact Executes.loopNil hs
  | @loop_false j p q s t u xs c d hs _ _ ip iq =>
    have hpop : (Memory.pop ⟨s,buf,hist⟩ j) = ⟨Function.update s j xs,buf,hist⟩ := by
      simp [Memory.pop, hs]
    have body : Executes a o (ofBitStack p) (Memory.pop ⟨s,buf,hist⟩ j) ⟨t,buf,hist⟩ c :=
      hpop ▸ ip
    simpa only [ofBitStack, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Executes.loopFalse hs body iq
  | @loop_true j p q s t u xs c d hs _ _ ip iq =>
    have hpop : (Memory.pop ⟨s,buf,hist⟩ j) = ⟨Function.update s j xs,buf,hist⟩ := by
      simp [Memory.pop, hs]
    have body : Executes a o (ofBitStack q) (Memory.pop ⟨s,buf,hist⟩ j) ⟨t,buf,hist⟩ c :=
      hpop ▸ ip
    simpa only [ofBitStack, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Executes.loopTrue hs body iq

/-- Embed a procedure in arbitrary disjoint scratch storage. The computation neither queries
an oracle nor looks at the buffered output and history. `bound` is the sibling's checked polynomial. -/
theorem procedure_exec {α β : Type} {ea : α → Word} {eb : β → Word} {f : α → β}
    (proc : Procedure ea eb f) (e : proc.K ↪ Fin k) (base : Store (Fin k)) (a : Fin k)
    (o : WordOracle) (buf : Word) (hist : Transcript) (x : α) :
    ∃ steps ≤ proc.bound.eval (ea x).length, Executes a o (ofBitStack (proc.program.relabel e))
      ⟨overlay e base (singletonStore proc.input (ea x)), buf, hist⟩
      ⟨overlay e base (singletonStore proc.output (eb (f x))), buf, hist⟩ steps := by
  obtain ⟨n,hn,run⟩ := proc.runs x
  exact ⟨n, hn, ofBitStack_exec (run.relabel e base) a o buf hist⟩

end BitCode
end OracleSpec
end LinearProgramming
end Optimization
end OAI
