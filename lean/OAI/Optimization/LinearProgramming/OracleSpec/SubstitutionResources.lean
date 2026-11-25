import OAI.Optimization.LinearProgramming.OracleSpec.CompilerProof
import Lean.Elab.Tactic.Omega

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace BitProgram

open BitCode

variable {p : BitProgram}

def Config.memory (c : p.Config) : Memory p.stackCount := ⟨c.store,c.bufferRev,c.transcript⟩

theorem tick_active (o : WordOracle) (c : p.Config) (i : Fin p.states) (h : c.pc = some i) :
    p.tick o c = some (perform p o c.memory (p.instruction i (c.store (p.scan i)).head?)) := by
  rcases c with ⟨pc,s,b,h₀⟩
  change pc = some i at h; subst pc
  unfold tick
  simp only [Option.bind_eq_bind,Option.bind_some]
  cases p.instruction i (s (p.scan i)).head? <;> rfl

theorem tick_decompose {o : WordOracle} {c d : p.Config} {k : ℕ}
    (h : p.tick o c = some (k,d)) :
    ∃ i, c.pc = some i ∧ perform p o c.memory (p.instruction i (c.store (p.scan i)).head?) = (k,d) := by
  cases hi : c.pc with
  | none => simp [tick,hi] at h
  | some i => exact ⟨i,rfl,Option.some.inj ((tick_active o c i hi).symm.trans h)⟩

/-- Bound every stack and the output buffer. An oracle instruction is charged for its complete
answer, which prevents an unaccounted-for blowup of the receiving stack. -/
def Config.Fits (c : p.Config) (B : ℕ) : Prop := c.bufferRev.length ≤ B ∧ ∀ i, (c.store i).length ≤ B

theorem fits_initial (p : BitProgram) (w : Word) : (p.initial w).Fits w.length := by
  refine ⟨Nat.zero_le _,?_⟩
  intro i
  by_cases h : i = p.inputStack <;> simp [initial,h]

theorem fits_step {o : WordOracle} {c d : p.Config} {k B : ℕ}
    (h : p.tick o c = some (k,d)) (hc : c.Fits B) : d.Fits (B+k) := by
  obtain ⟨i,_,e⟩ := tick_decompose h
  have frame : ∀ s, (c.store s).length ≤ B := hc.2
  have buffer := hc.1
  cases hI : p.instruction i (c.store (p.scan i)).head? with
  | jump j => rw [hI] at e; cases e; exact ⟨by dsimp [perform,place,Config.memory]; omega, fun s => (frame s).trans (by omega)⟩
  | push s bit j =>
    rw [hI] at e; cases e
    refine ⟨by dsimp [perform,place,Config.memory,Memory.push]; omega,?_⟩
    intro t
    by_cases h : t = s
    · subst t; simpa [perform,place,Config.memory,Memory.push] using frame s
    · exact (by simpa [perform,place,Config.memory,Memory.push,h] using (frame t).trans (Nat.le_succ B))
  | pop s j =>
    rw [hI] at e; cases e
    refine ⟨by dsimp [perform,place,Config.memory,Memory.pop]; omega,?_⟩
    intro t
    by_cases h : t = s
    · subst t; simp [place,Config.memory,Memory.pop,List.length_tail]
      have := frame s; omega
    · simpa [perform,place,Config.memory,Memory.pop,h] using (frame t).trans (Nat.le_succ B)
  | emit bit j =>
    rw [hI] at e; cases e
    exact ⟨by simpa [perform,place,Config.memory,Memory.emit] using buffer,
      fun s => (frame s).trans (by omega)⟩
  | ask j =>
    rw [hI] at e; cases e
    refine ⟨Nat.zero_le _,?_⟩
    intro t
    by_cases h : t = p.answerStack
    · subst t; simp [place,Config.memory,Memory.receive]; omega
    · simp [place,Config.memory,Memory.receive,h]
      have := frame t; omega
  | halt => rw [hI] at e; cases e; exact ⟨buffer.trans (by omega),fun s => (frame s).trans (by omega)⟩

theorem Run.fits {o : WordOracle} {c d : p.Config} {k B : ℕ} (h : p.Run o c k d)
    (hc : c.Fits B) : d.Fits (B+k) := by
  induction h generalizing B with
  | refl => simpa using hc
  | step ht _ ih => simpa [Nat.add_assoc] using ih (fits_step ht hc)

theorem tick_history_le {o : WordOracle} {c d : p.Config} {k : ℕ} (h : p.tick o c = some (k,d)) :
    c.transcript.length ≤ d.transcript.length := by
  obtain ⟨i,_,e⟩ := tick_decompose h
  cases hI : p.instruction i (c.store (p.scan i)).head? <;> rw [hI] at e <;> cases e <;>
    simp [place,Config.memory,Memory.push,Memory.pop,Memory.emit,Memory.receive]

theorem Run.history_le {o : WordOracle} {c d : p.Config} {k : ℕ} (h : p.Run o c k d) :
    c.transcript.length ≤ d.transcript.length := by
  induction h with
  | refl => exact le_rfl
  | step ht _ ih => exact (tick_history_le ht).trans ih

/-- Every exchange in a prefix remains in the recorded final transcript. -/
theorem tick_mem_history {o : WordOracle} {c d : p.Config} {k : ℕ} (h : p.tick o c = some (k,d))
    {item : Word × Word} (mem : item ∈ c.transcript) : item ∈ d.transcript := by
  obtain ⟨i,_,e⟩ := tick_decompose h
  cases hI : p.instruction i (c.store (p.scan i)).head? <;> rw [hI] at e <;> cases e <;>
    first | exact mem | exact List.mem_cons_of_mem _ mem

theorem Run.mem_history {o : WordOracle} {c d : p.Config} {k : ℕ} (h : p.Run o c k d)
    {item : Word × Word} (mem : item ∈ c.transcript) : item ∈ d.transcript := by
  induction h with
  | refl => exact mem
  | step ht _ ih => exact ih (tick_mem_history ht mem)

end BitProgram
end OracleSpec
end LinearProgramming
end Optimization
end OAI
