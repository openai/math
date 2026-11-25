import OAI.Hierarchy.ProtocolRAMSchedule
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Sequential purchase jobs on a common frozen input

Each job may update its own region while preserving the common input, the
readiness of other jobs, and their completed outputs. Sequencing the native
procedures in a duplicate-free order preserves all completed outputs.
-/

namespace Hierarchy.ProtocolRAMFrozenSweep

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.PhysicalProcedure
open scoped BigOperators

variable {w : ℕ} {ι : Type*}

attribute [local irreducible] Procedure.Exec

/-- Run the listed procedures in chronological order, followed by the empty scan. -/
def program (cpu : ι → Procedure w) : List ι → Procedure w
  | [] => ProtocolRAM.program w []
  | i :: rest => (cpu i).seq (program cpu rest)

/-- The empty scan costs four instructions. -/
def clock (ticks : ι → ℕ) (order : List ι) : ℕ := (order.map ticks).sum + 4

/-- The physical output is the chronological composition of the memory updates. -/
def output (f : ι → Memory w → Memory w) (order : List ι) (m : Memory w) : Memory w :=
  order.foldl (fun cur i => f i cur) m

@[simp] theorem output_nil (f : ι → Memory w → Memory w) (m : Memory w) : output f [] m = m := rfl

@[simp] theorem output_cons (f : ι → Memory w → Memory w) (i : ι) (rest : List ι) (m : Memory w) :
    output f (i :: rest) m = output f rest (f i m) := rfl

/-- Each job preserves the shared input and the local state of every other job. -/
def Step (cpu : ι → Procedure w) (ticks : ι → ℕ) (shared : Memory w → Prop)
    (ready done : ι → Memory w → Prop) : Prop :=
  ∀ i m, shared m → ready i m → ∃ out,
    (cpu i).Exec m out (ticks i) ∧ shared out ∧ done i out ∧
      (∀ j, j ≠ i → ready j m → ready j out) ∧
      (∀ j, j ≠ i → done j m → done j out)

/-- Per-job execution with a specified total memory update. -/
def StepAt (cpu : ι → Procedure w) (ticks : ι → ℕ) (f : ι → Memory w → Memory w)
    (shared : Memory w → Prop) (ready done : ι → Memory w → Prop) : Prop :=
  ∀ i m, shared m → ready i m →
    (cpu i).Exec m (f i m) (ticks i) ∧ shared (f i m) ∧ done i (f i m) ∧
      (∀ j, j ≠ i → ready j m → ready j (f i m)) ∧
      (∀ j, j ≠ i → done j m → done j (f i m))

/-- Execute the prescribed memory updates once in the specified order. -/
theorem run_list_exact (cpu : ι → Procedure w) (ticks : ι → ℕ) (f : ι → Memory w → Memory w)
    (shared : Memory w → Prop) (ready done : ι → Memory w → Prop)
    (step : StepAt cpu ticks f shared ready done) (order : List ι)
    (distinct : order.Nodup) (m : Memory w) (common : shared m)
    (prepared : ∀ i ∈ order, ready i m) :
    let out := output f order m
    (program cpu order).Exec m out (clock ticks order) ∧ shared out ∧
      (∀ i ∈ order, done i out) ∧ (∀ j ∉ order, done j m → done j out) := by
  dsimp only
  induction order generalizing m with
  | nil =>
    refine ⟨?_, common, by simp, fun _ _ h => h⟩
    exact ProtocolRAM.program_exec [] m (by simp)
  | cons i rest ih =>
    obtain ⟨fresh, tailDistinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨firstRun, sharedNext, finished, readyFrame, doneFrame⟩ :=
      step i m common (prepared i (List.mem_cons_self ..))
    have readyNext (j : ι) (hj : j ∈ rest) : ready j (f i m) :=
      readyFrame j (fun eqn => fresh (eqn ▸ hj)) (prepared j (List.mem_cons_of_mem i hj))
    obtain ⟨tailRun, sharedOut, tailDone, tailFrame⟩ :=
      ih (m := f i m) tailDistinct sharedNext readyNext
    refine ⟨?_, sharedOut, ?_, ?_⟩
    · simpa only [program, output_cons, clock, List.map_cons, List.sum_cons, Nat.add_assoc] using
        firstRun.then tailRun
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | member
      · exact tailFrame _ fresh finished
      · exact tailDone j member
    · intro j hj old
      have ne : j ≠ i := fun eqn => hj (List.mem_cons.mpr (.inl eqn))
      exact tailFrame j (fun h => hj (List.mem_cons_of_mem i h)) (doneFrame j ne old)

/-- A sweep also preserves the completed outputs when jobs are specified existentially. -/
theorem run_list (cpu : ι → Procedure w) (ticks : ι → ℕ) (shared : Memory w → Prop)
    (ready done : ι → Memory w → Prop) (step : Step cpu ticks shared ready done) (order : List ι)
    (distinct : order.Nodup) (m : Memory w) (common : shared m)
    (prepared : ∀ i ∈ order, ready i m) :
    ∃ out, (program cpu order).Exec m out (clock ticks order) ∧ shared out ∧
      (∀ i ∈ order, done i out) ∧ (∀ j ∉ order, done j m → done j out) := by
  classical
  let f (i : ι) (x : Memory w) : Memory w :=
    if h : shared x ∧ ready i x then (step i x h.1 h.2).choose else x
  have fixed : StepAt cpu ticks f shared ready done := by
    intro i x hc hr
    simpa only [f, dite_eq_left (And.intro hc hr)] using (step i x hc hr).choose_spec
  exact ⟨output f order m, run_list_exact cpu ticks f shared ready done fixed order distinct m
    common prepared⟩

/-- All indexed jobs execute into the single explicit final image. -/
theorem run_exact {q : ℕ} (cpu : Fin q → Procedure w) (ticks : Fin q → ℕ)
    (f : Fin q → Memory w → Memory w) (shared : Memory w → Prop)
    (ready done : Fin q → Memory w → Prop) (step : StepAt cpu ticks f shared ready done)
    (m : Memory w) (common : shared m) (prepared : ∀ i, ready i m) :
    let out := output f (List.finRange q) m
    (program cpu (List.finRange q)).Exec m out ((∑ i, ticks i) + 4) ∧
      shared out ∧ ∀ i, done i out := by
  obtain ⟨ran, sharedOut, complete, _⟩ := run_list_exact cpu ticks f shared ready done step
    (List.finRange q) (List.nodup_finRange q) m common (fun i _ => prepared i)
  refine ⟨?_, sharedOut, fun i => complete i (List.mem_finRange i)⟩
  simpa only [clock, List.finRange, List.map_ofFn, Function.comp_def, List.sum_ofFn] using ran

/-- Executing every indexed job once leaves every output available in one physical memory. -/
theorem run {q : ℕ} (cpu : Fin q → Procedure w) (ticks : Fin q → ℕ) (shared : Memory w → Prop)
    (ready done : Fin q → Memory w → Prop) (step : Step cpu ticks shared ready done)
    (m : Memory w) (common : shared m) (prepared : ∀ i, ready i m) :
    ∃ out, (program cpu (List.finRange q)).Exec m out ((∑ i, ticks i) + 4) ∧
      shared out ∧ ∀ i, done i out := by
  obtain ⟨out, ran, sharedOut, complete, _⟩ := run_list cpu ticks shared ready done step
    (List.finRange q) (List.nodup_finRange q) m common (fun i _ => prepared i)
  refine ⟨out, ?_, sharedOut, fun i => complete i (List.mem_finRange i)⟩
  simpa only [clock, List.finRange, List.map_ofFn, Function.comp_def, List.sum_ofFn] using ran

end Hierarchy.ProtocolRAMFrozenSweep

end OAI
