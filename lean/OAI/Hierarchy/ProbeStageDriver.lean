import OAI.ThreeFlat.RAM.PhysicalExactRun
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI
/-! # Chronological native driver of the deterministic subdivision records -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators

/-- The ordinal is part of the fixed instruction layout; its private inputs,
colors and updates are determined at run time. The fixed initialization
procedure executes once, followed by the record bodies in increasing order. -/
def chronological {w : ℕ} (initial : Procedure w) (record : ℕ → Procedure w) : ℕ → Procedure w
  | 0 => initial
  | n+1 => (chronological initial record n).seq (record n)

theorem chronological_exec {w n : ℕ} (initial : Procedure w) (record : ℕ → Procedure w)
    (input : Memory w) (state : ℕ → Memory w) (startup : ℕ) (work : ℕ → ℕ)
    (first : initial.Exec input (state 0) startup)
    (actual : ∀ i<n, (record i).Exec (state i) (state (i+1)) (work i)) :
    (chronological initial record n).Exec input (state n) (startup+∑ i ∈ Finset.range n,work i) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero,Nat.add_zero]
    exact @first
  | succ n ih =>
    rw [Finset.sum_range_succ,← Nat.add_assoc]
    apply Procedure.Exec.then
    · exact ih (fun i hi => actual i (Nat.lt_succ_of_lt hi))
    · exact actual n (Nat.lt_succ_self _)

/-- Each unrolled row contributes its actual finite instruction and public
word counts, including the statically linked register banks. -/
theorem chronological_dimensions {w : ℕ} (initial : Procedure w) (record : ℕ → Procedure w) (n : ℕ) :
    (chronological initial record n).labels = initial.labels+∑ i ∈ Finset.range n,(record i).labels ∧
    (chronological initial record n).slots = initial.slots+∑ i ∈ Finset.range n,(record i).slots := by
  induction n with
  | zero => simp [chronological]
  | succ n ih =>
    simp only [chronological,Procedure.seq,Finset.sum_range_succ,ih.1,ih.2,Nat.add_assoc,and_self]

theorem chronological_registers {w : ℕ} (initial : Procedure w) (record : ℕ → Procedure w) (n : ℕ) :
    (chronological initial record n).registers =
      initial.registers+∑ i ∈ Finset.range n,(record i).registers := by
  induction n with
  | zero => simp [chronological]
  | succ n ih =>
    change (chronological initial record n).registers+(record n).registers = _
    rw [ih,Finset.sum_range_succ,Nat.add_assoc]

end Hierarchy.ProbeStage.Native

end OAI
