import OAI.ThreeFlat.Diagonal.HistogramAdmission
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Deterministic admission of a compression-stage histogram

The physical guard checks the counts at their word addresses. Its terminating instruction
agrees with the parser for the corresponding canonical bit string, including inactive
letters, and its running time counts the actual number of rows in the stage.
-/

noncomputable section
namespace Hierarchy.TraceAdmission

open ThreeFlat Diagonal.HistogramRegister
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.ContinuationLink
open scoped Classical Fin.CommRing

variable {M K W count : ℕ}

/-- The typed parser and the word-level admission test accept exactly the same record. -/
theorem read_record_iff (rows : Rows M K W) (order : Fin count ≃ Choices rows)
    (x : Words M K W) :
    ((record rows order).read (List.ofFn (bitTable x))).isSome ↔ admitted rows x := by
  constructor
  · intro parsed
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp parsed
    have encoded := (record rows order).write_read _ i hi
    change List.ofFn (bitTable (words rows (order i))) = List.ofFn (bitTable x) at encoded
    have same := bitTable.injective (List.ofFn_injective encoded)
    exact same ▸ admit_words rows (order i)
  · intro valid
    let i := order.symm (choices rows x valid)
    have encoded : (record rows order).write i = List.ofFn (bitTable x) := by
      change List.ofFn (bitTable (words rows (order i))) = _
      simp [i]
    rw [← encoded, (record rows order).read_write]
    rfl

/-- Embed the actual finite row-check ROM and close its successful exit with acceptance. -/
def rowGuard (ctrl K W : ℕ) :=
  close (AdmissionBank.block (w := W) (k := 0) ctrl K) (0 : Fin 1)
    (fun _ _ => .accept) Fin.elim0

/-- A fixed program, independent of the counts, checks the canonical stage in a number of
steps linear in the number of rows. Both outcomes preserve memory. -/
theorem rowGuard_stops (ctrl : ℕ) (hw : 0 < W) (rows : Rows M K W)
    (order : Fin count ≃ Choices rows) (x : Words M K W) (mem : Memory W)
    (layout : BankLayout ctrl rows x mem) (room : AdmissionBank.Fits ctrl K mem) (state : Word W) :
    let guard := rowGuard ctrl K W
    ∃ t ≤ 6 + M * (2 * AdmissionBank.cost 0 K + 4), ∃ out,
      advance guard.program t (guard.program.start state) mem = some (out, mem) ∧
      guard.code out.pc = if ((record rows order).read (List.ofFn (bitTable x))).isSome
        then .accept else .reject := by
  let block := AdmissionBank.block (w := W) (k := 0) ctrl K
  let guard := rowGuard ctrl K W
  have installed := close_installed block (0 : Fin 1) (fun _ _ => .accept) Fin.elim0
  obtain ⟨t, ht, out, run, destination, bad⟩ :=
    AdmissionBank.advance_block ctrl K hw _ _ _ _ guard installed (guard.program.start state)
      mem rfl room
  rw [AdmissionBank.cost_eq ctrl K, layout.count] at ht
  refine ⟨t, ht, out, run, ?_⟩
  have accepts := (valid_rows_iff_admitted layout).trans (read_record_iff rows order x).symm
  rw [destination]
  by_cases valid : ((record rows order).read (List.ofFn (bitTable x))).isSome
  · rw [ite_eq_left (accepts.mpr valid), ite_eq_left valid]
    exact close_tail block (0 : Fin 1) (fun _ _ => .accept) Fin.elim0 0
  · rw [ite_eq_right (fun h => valid (accepts.mp h)), ite_eq_right valid]
    exact bad

/-- A malformed histogram has zero weight at the fixed budget and at every larger fuel. -/
theorem rowGuard_reject_mass {F : Type*} [Semiring F] (field : FieldCode F W)
    (ctrl : ℕ) (hw : 0 < W) (rows : Rows M K W) (order : Fin count ≃ Choices rows)
    (x : Words M K W) (mem : Memory W) (layout : BankLayout ctrl rows x mem)
    (room : AdmissionBank.Fits ctrl K mem) (state : Word W)
    (bad : (record rows order).read (List.ofFn (bitTable x)) = none) (extra : ℕ) :
    let guard := rowGuard ctrl K W
    mass field guard.program (extra + (6 + M * (2 * AdmissionBank.cost 0 K + 4)))
      (guard.program.start state) mem = 0 := by
  let block := AdmissionBank.block (w := W) (k := 0) ctrl K
  let guard := rowGuard ctrl K W
  have invalid : ¬∀ i, i < AdmissionBank.rowCount ctrl mem → AdmissionBank.ValidRow ctrl K i mem := by
    intro h
    have valid := (read_record_iff rows order x).mpr ((valid_rows_iff_admitted layout).mp h)
    simp [bad] at valid
  have installed := close_installed block (0 : Fin 1) (fun _ _ => .accept) Fin.elim0
  simpa only [layout.count] using AdmissionBank.reject_mass field ctrl K hw _ _ _ _ guard installed
    (guard.program.start state) mem rfl room invalid extra


end Hierarchy.TraceAdmission

end
end OAI
