import OAI.Optimization.LinearProgramming.RAM.Basic
import Mathlib.Data.Fin.Basic

/-! Composing counted executions while retaining the size invariant at *every* state. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Each edge is one actual instruction. `safe` is checked at both endpoints and every
state traversed in between. -/
inductive Execution (p : Program) (safe : State K → Prop) : State K → Nat → State K → Prop where
  | done (s : State K) (hs : safe s) : Execution p safe s 0 s
  | next {s t z : State K} {k : Nat} (hs : safe s) (step_eq : step p s = some t)
      (rest : Execution p safe t k z) : Execution p safe s (k + 1) z

namespace Execution

variable {p : Program} {safe : State K → Prop} {s t z : State K} {k l : Nat}

theorem append (h : Execution p safe s k t) (g : Execution p safe t l z) :
    Execution p safe s (k + l) z := by
  induction h with
  | done _ _ => simpa using g
  | next hsafe hstep _ ih =>
    simpa only [Nat.succ_add] using Execution.next hsafe hstep (ih g)

theorem safe_start (h : Execution p safe s k t) : safe s := by
  cases h with
  | done _ hs => exact hs
  | next hs _ _ => exact hs

theorem safe_end (h : Execution p safe s k t) : safe t := by
  induction h with
  | done _ hs => exact hs
  | next _ _ _ ih => exact ih

theorem one (hs : safe s) (h : step p s = some t) (ht : safe t) :
    Execution p safe s 1 t := .next hs h (.done t ht)

/-- Reverse the chronological trace representation in the public machine contract into a
composable proof. No unobserved machine transitions are inserted. -/
theorem of_trace {k : Nat} {trace : Fin (k+1) → State K}
    (h : Trace p s k trace) (hs : ∀ i, safe (trace i)) :
    Execution p safe s k (trace (Fin.last k)) := by
  induction k generalizing s with
  | zero =>
    have hz : trace (Fin.last 0) = s := h.1
    rw [hz]
    exact .done s (h.1 ▸ hs 0)
  | succ k ih =>
    let tail : Fin (k+1) → State K := fun i => trace i.succ
    have ht : Trace p (tail 0) k tail := ⟨rfl, fun i => h.2 i.succ⟩
    have first := h.2 0
    rw [show trace (0 : Fin (k+1)).castSucc = s from h.1] at first
    exact .next (h.1 ▸ hs 0) first (ih ht (fun i => hs i.succ))

/-- Extract the register trace with its time and scalar-size bounds. -/
theorem to_trace (h : Execution p safe s k t) :
    ∃ trace : Fin (k+1) → State K,
      Trace p s k trace ∧ trace (Fin.last k) = t ∧ ∀ i, safe (trace i) := by
  induction h with
  | done s hs => exact ⟨fun _ => s, ⟨rfl, Fin.elim0⟩, rfl, fun _ => hs⟩
  | @next s t z k hs hstep rest ih =>
    obtain ⟨tail, htail, hend, hsafe⟩ := ih
    let trace : Fin (k+2) → State K := Fin.cases s tail
    refine ⟨trace, ⟨rfl, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change step p s = some (tail 0)
        rw [htail.1]
        exact hstep
      · simpa [trace] using htail.2 j
    · change tail (Fin.last k) = z
      exact hend
    · exact Fin.cases hs hsafe

end Execution

/-- `code` occupies a contiguous interval of the program starting at `pc`. -/
def CodeAt (p : Program) (pc : Nat) (code : List Instr) : Prop :=
  ∃ pre post : List Instr, pre.length = pc ∧ p = pre ++ code ++ post

namespace CodeAt

theorem whole (code : List Instr) : CodeAt code 0 code := ⟨[], [], rfl, by simp⟩

theorem left {p pc a b} (h : CodeAt p pc (a ++ b)) : CodeAt p pc a := by
  obtain ⟨pre, post, hlen, rfl⟩ := h
  exact ⟨pre, b ++ post, hlen, by simp [List.append_assoc]⟩

theorem right {p pc a b} (h : CodeAt p pc (a ++ b)) : CodeAt p (pc+a.length) b := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre ++ a, post, by simp, by simp [List.append_assoc]⟩

theorem head {p pc i rest} (h : CodeAt p pc (i :: rest)) : p[pc]? = some i := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  simp [List.append_assoc]

end CodeAt
end RAM
end LinearProgramming
end Optimization
end OAI
