import OAI.ThreeFlat.RAM.ProcedureBank
import OAI.ThreeFlat.RAM.PhysicalExactRun
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Sequential execution of finite boards preserving earlier publications -/

namespace Hierarchy.ProtocolRAMFrozenSeries

open Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators

/-- Run the linked procedures in increasing index order. Every previously
published board and the initial protected memory survive the final stage.
The execution budget is the sum of the individual stage budgets. -/
theorem run_observed {W : ℕ} (m : ℕ) :
    ∀ (phase : Fin (m+1) → Procedure W) (mem : Memory W) (ready : Memory W → Prop)
      (kept : ℕ → Prop) (board : Fin (m+1) → ℕ → Prop) (readback : Fin (m+1) → ℕ → Word W → Prop)
      (cost : Fin (m+1) → ℕ), ready mem →
      (∀ j s, ready s → ∃ t, (phase j).Exec s t (cost j) ∧ ready t ∧
        (∀ a, board j a → readback j a (t a)) ∧ (∀ a, kept a → t a = s a) ∧
        (∀ i, i < j → ∀ a, board i a → t a = s a)) →
      ∃ tail, (ProcedureBank.program m phase).Exec mem tail (∑ j, cost j) ∧ ready tail ∧
        (∀ j a, board j a → readback j a (tail a)) ∧ (∀ a, kept a → tail a = mem a) := by
  induction m with
  | zero =>
    intro phase mem ready kept board readback cost initial step
    obtain ⟨tail,exec,done,published,frame,_⟩ := step 0 mem initial
    refine ⟨tail,?_,done,?_,frame⟩
    · have one : (∑ j, cost j) = cost 0 := by simp
      rw [one]
      change (phase 0).Exec mem tail (cost 0)
      exact @exec
    · intro j
      have hj : j = 0 := Fin.ext (by change j.val = 0; have := j.isLt; omega)
      rw [hj]
      exact published
  | succ m ih =>
    intro phase mem ready kept board readback cost initial step
    obtain ⟨next,first,canStart,published,frame,_⟩ := step 0 mem initial
    let protect := fun a => kept a ∨ board 0 a
    have later (j : Fin (m+1)) (s : Memory W) (canRun : ready s) :
        ∃ t, (phase j.succ).Exec s t (cost j.succ) ∧ ready t ∧
          (∀ a, board j.succ a → readback j.succ a (t a)) ∧ (∀ a, protect a → t a = s a) ∧
          (∀ i : Fin (m+1), i < j → ∀ a, board i.succ a → t a = s a) := by
      obtain ⟨t,exec,done,put,old,previous⟩ := step j.succ s canRun
      refine ⟨t,exec,done,put,?_,?_⟩
      · intro a ha
        rcases ha with hk | hfirst
        · exact old a hk
        · exact previous 0 (Fin.succ_pos j) a hfirst
      · intro i before
        exact previous i.succ (Fin.succ_lt_succ_iff.mpr before)
    obtain ⟨tail,rest,done,suffix,unchanged⟩ := ih (fun j => phase j.succ) next ready protect
      (fun j => board j.succ) (fun j => readback j.succ) (fun j => cost j.succ) canStart later
    refine ⟨tail,?_,done,?_,fun a ha => (unchanged a (Or.inl ha)).trans (frame a ha)⟩
    · rw [ProcedureBank.program,Fin.sum_univ_succ]
      exact first.then rest
    · intro j
      refine Fin.cases ?_ (fun i => suffix i) j
      intro a ha
      rw [unchanged a (Or.inr ha)]
      exact published a ha

/-- Exact board values are the special case in which each readback checks
equality of the full native word. -/
theorem run {W : ℕ} (m : ℕ) (phase : Fin (m+1) → Procedure W) (mem : Memory W)
    (ready : Memory W → Prop) (kept : ℕ → Prop) (board : Fin (m+1) → ℕ → Prop)
    (word : Fin (m+1) → ℕ → Word W) (cost : Fin (m+1) → ℕ) (initial : ready mem)
    (step : ∀ j s, ready s → ∃ t, (phase j).Exec s t (cost j) ∧ ready t ∧
      (∀ a, board j a → t a = word j a) ∧ (∀ a, kept a → t a = s a) ∧
      (∀ i, i < j → ∀ a, board i a → t a = s a)) :
    ∃ tail, (ProcedureBank.program m phase).Exec mem tail (∑ j, cost j) ∧ ready tail ∧
      (∀ j a, board j a → tail a = word j a) ∧ (∀ a, kept a → tail a = mem a) :=
  run_observed m phase mem ready kept board (fun j a v => v = word j a) cost initial step


end Hierarchy.ProtocolRAMFrozenSeries

end OAI
