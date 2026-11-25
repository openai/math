import OAI.Computability.BorderVNP.FiniteDiagonalCellTracePositive
import OAI.Computability.BorderVNP.CellDirectorySigns

/-! # Positive native auxiliary tapes for arbitrary unsigned sparse directories

Truth-table guards, unary tests, field gadget factors, repeated equalities and
profile constraints all preserve the sign of individual traces. This applies
to packed bottom boxes with zero padding and to inherited public guards.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace

open CellSparse CellMacro Copied
open private SafeStmt PreservesSign preserves guardSafe fixed seq loop cond list sweepSafe totalsSafe signFalseSafe
  from OAI.Computability.BorderVNP.FiniteDiagonalCellTracePositive

/-- A stored factor has no signed entry table. -/
abbrev UnsignedFactor := Factor.SignFree

/-- Every stored factor in the directory preserves the sign of a passing trace. -/
abbrev UnsignedDirectory := Directory.SignFree

private theorem profileSafe (copies : ℕ) (selector : CellSparse.Port) (w : ℕ) (hist : List ℕ) (routes : List Route) :
    SafeStmt (profileRow copies selector w hist routes) := by
  apply seq (loop _ (fixed .guess (by decide))) _
  apply seq _ (loop _ (seq (fixed _ (by decide)) (seq (fixed _ (by decide)) (fixed _ (by decide)))))
  apply seq (loop _ (guardSafe _)) _
  apply seq
  · apply list
    intro s hs
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hs
    exact seq (seq (loop _ (cond _ _ (guardSafe _) (guardSafe _)))
      (loop _ (loop _ (cond _ _ (guardSafe _) (guardSafe _))))) (guardSafe _)
  · apply list
    intro s hs
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hs
    exact seq (guardSafe _) (loop _ (loop _ (loop _ (guardSafe _))))

private theorem recordSafe (boxes : List (List Factor)) (r : Record) : SafeStmt (recordGuard boxes r) := by
  cases r with
  | zero | equal => exact loop _ (loop _ (guardSafe _))
  | box => exact guardSafe _
  | profile c s w h rs => exact profileSafe c s w h rs

private theorem safeFields (D : Directory) (h : UnsignedDirectory D) : SafeStmt D.checkAssignment := by
  apply seq _ (seq _ (totalsSafe D))
  · apply list
    intro s hs
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hs
    exact recordSafe _ _
  · apply sweepSafe
    intro b hb f hf ix off copy
    obtain ⟨r,hr,hb'⟩ := List.mem_filterMap.mp hb
    cases r with
    | zero | equal | profile => contradiction
    | box id base count stride =>
      obtain rfl := Option.some.inj hb'
      change f ∈ D.boxes.getD id [] at hf
      rw [List.getD_eq_getElem?_getD] at hf
      cases pick : D.boxes[id]? with
      | none => simp [pick] at hf
      | some box =>
        simp only [pick,Option.getD_some] at hf
        have safe := h box (List.mem_of_getElem? pick) f hf
        cases f with
        | sign => exact safe.elim
        | truth | gadget | unary => exact seq (guardSafe _) signFalseSafe

/-- No signed auxiliary cancellation is possible in the real bytecode traces
of an unsigned sparse field directory, including all profile and subtotal rows. -/
theorem unsigned_positive (D : Directory) (h : UnsignedDirectory D) (e : List ℕ) (wires ext tail : List Bool) (sg : Bool)
    (run : (tail,sg) ∈ Compact.assignmentTails D e wires ext) : sg = false :=
  preserves (safeFields D h e) ⟨true,false⟩ _ _ _ run

/-- Exact unsigned native tape count at a fixed initial wire assignment. -/
theorem unsigned_card (D : Directory) (h : UnsignedDirectory D) (e : List ℕ) (wires ext : List Bool) :
    ((Compact.assignmentTails D e wires ext).card : ℤ) = D.weight (lookup (wires ++ ext)) := by
  rw [← Compact.assignmentTails_sum D e wires ext]
  let T := Compact.assignmentTails D e wires ext
  change (T.card : ℤ) = ∑ p ∈ T, TeamTape.haltWeight true p.2
  calc (T.card : ℤ) = ∑ _ ∈ T, (1 : ℤ) := by simp
       _ = _ := by
         apply Finset.sum_congr rfl
         rintro ⟨tail,sg⟩ ht
         rw [unsigned_positive D h e wires ext tail sg ht]
         rfl

end FiniteDiagonal.CellTrace

end BorderVNP
end Computability
end OAI
