import OAI.Computability.BorderVNP.CubeLabelStages
import OAI.Computability.BorderVNP.CubeMeanPhysicalTables
import Mathlib.Data.List.TakeDrop

/-! # The ascending RAM stages return the sparse scan's physical packing codes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open Cube Cube.MeanChoice

variable {n : ℕ} {I : Type*} [Fintype I]

/-- The forward ordinal loop and the list-based recursive sparse scan have the same
result at their normal end, including the case of an empty set of cells. -/
theorem stage_eq_scanNat (rows : I → Traffic (Fin n)) (z : ℕ) :
    stage rows z n = scanNat rows (List.finRange n) ∅ (fun _ => 0) (cache rows ∅ (fun _ => 0)) := by
  let rest (k : ℕ) := scanNat rows ((List.finRange n).drop k) (cellsBefore n k)
    (stage rows z k) (cache rows (cellsBefore n k) (stage rows z k))
  have step (k : ℕ) (h : k < n) : rest k = rest (k+1) := by
    let c : Fin n := ⟨k,h⟩
    have split : (List.finRange n).drop k = c :: (List.finRange n).drop (k+1) := by
      have len : k < (List.finRange n).length := by simpa using h
      have front : (List.finRange n)[k] = c := List.getElem_finRange len
      exact (List.cons_getElem_drop_succ (h := len)).symm.trans
        (congrArg (fun a => a :: (List.finRange n).drop (k+1)) front)
    have fresh : c ∉ cellsBefore n k := by simp [c,cellsBefore]
    dsimp only [rest]
    rw [split,scanNat,ite_eq_right fresh,stage,dite_eq_left h,cellsBefore_succ h]
    simp only [scoreNat,commit_cache]
    rfl
  have all (k : ℕ) (h : k ≤ n) : rest 0 = rest k := by
    induction k with
    | zero => rfl
    | succ k ih => exact (ih (by omega)).trans (step k (by omega))
  have h := all n le_rfl
  have done : (List.finRange n).drop n = [] := List.drop_eq_nil_iff.mpr (by simp)
  simpa [rest,done,cellsBefore,scanNat,stage] using h.symm

/-- Applied to the actual decoded traffic arrays, the last native ordinal stage is the
input used by the physical balanced-label calculation. -/
theorem stage_tables (l : Cube.LabelIndex.Layout) (m : ℕ → ℕ) (ep : Cube.LabelIndex.Endpoints l m) (z : ℕ) :
    stage (Cube.LabelIndex.fromTables l m ep) z l.cells = Cube.Physical.tableCodes l m ep z :=
  stage_eq_scanNat _ _

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
