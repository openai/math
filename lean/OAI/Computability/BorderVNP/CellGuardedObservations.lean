import OAI.Computability.BorderVNP.CellDirectorySigns
import OAI.Computability.BorderVNP.CellDirectoryObservationLedger

/-! # Ordered signed observation lists after the public wiring checks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open scoped Classical

/-- Complete observed list for a private assignment whose public rows pass.
Subtotal words are checked separately against this list. -/
noncomputable def Directory.guardedObservations (D : Directory) (bank : ℕ → Bool) :
    Option (List (Bool × Option ℕ)) :=
  if ∀ r ∈ D.records, r.Valid D.boxes bank then D.observations bank else none

theorem Directory.guarded_some {D : Directory} {bank : ℕ → Bool} {os : List (Bool × Option ℕ)} :
    D.guardedObservations bank = some os ↔ (∀ r ∈ D.records, r.Valid D.boxes bank) ∧ D.observations bank=some os := by
  classical
  unfold guardedObservations
  split_ifs <;> simp_all

private def combine {α : Type*} (x y : Option (List α)) : Option (List α) := do
  return (← x)++(← y)

/-- Two row groups on a common box table concatenate their checked observations
exactly when both groups succeed. -/
private theorem append_groups (tables : List (List Factor)) (xs ys : List Record) (bank : ℕ → Bool) :
    (⟨tables,xs++ys,[]⟩ : Directory).guardedObservations bank =
      combine ((⟨tables,xs,[]⟩ : Directory).guardedObservations bank)
        ((⟨tables,ys,[]⟩ : Directory).guardedObservations bank) := by
  classical
  have splitRead : (⟨tables,xs++ys,[]⟩ : Directory).observations bank =
      combine ((⟨tables,xs,[]⟩ : Directory).observations bank)
        ((⟨tables,ys,[]⟩ : Directory).observations bank) := by
    simp only [Directory.observations,Directory.occurrences,List.flatMap_append,List.mapM_append,combine]
  have right (v : Option (List (Bool × Option ℕ))) : combine v none = none := by cases v <;> rfl
  have left (v : Option (List (Bool × Option ℕ))) : combine none v = none := rfl
  simp only [Directory.guardedObservations,List.forall_mem_append,splitRead]
  split_ifs <;> first | rfl | exact (right _).symm | exact (left _).symm | tauto

/-- Replacing each row group's bank by one with the same complete checked
observations preserves the exact merged list, in row order. -/
theorem Directory.flatMap_guarded_congr {ι : Type*} (sites : List ι) (tables : List (List Factor))
    (rows : ι → List Record) (a b : ℕ → Bool) (h : ∀ v ∈ sites,
      (⟨tables,rows v,[]⟩ : Directory).guardedObservations a =
        (⟨tables,rows v,[]⟩ : Directory).guardedObservations b) :
    (⟨tables,sites.flatMap rows,[]⟩ : Directory).guardedObservations a =
      (⟨tables,sites.flatMap rows,[]⟩ : Directory).guardedObservations b := by
  induction sites with
  | nil => simp [Directory.guardedObservations,Directory.observations,Directory.occurrences]
  | cons v vs ih =>
    rw [List.flatMap_cons,append_groups,append_groups,h v List.mem_cons_self,ih (fun j hj => h j (.tail _ hj))]

theorem Directory.SignFree.weight_guarded {D : Directory} (h : D.SignFree) (bank : ℕ → Bool) :
    D.weight bank = if ∃ os, D.guardedObservations bank = some os ∧ countsValid bank D.reportedCounts os then 1 else 0 := by
  rw [h.weight_eq]
  congr 1
  apply propext
  simp only [Directory.guarded_some]
  constructor <;> rintro ⟨os,hs⟩
  · exact ⟨os,⟨hs.2.1,hs.1⟩,hs.2.2⟩
  · exact ⟨os,hs.1.2,hs.1.1,hs.2⟩

end CellSparse

end BorderVNP
end Computability
end OAI
