import OAI.Computability.BorderVNP.CellGadgetSteps
import OAI.Computability.BorderVNP.CellGadgetAux
import OAI.Computability.BorderVNP.CellRecordGuards

/-! # Exact multiplicity-one compilation of announced gadget subtotals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro
open scoped Classical

namespace Gadget

/-- Check a whole one-hot prefix table followed by the announced binary count. -/
def checker (D : Directory) (id : ℕ) (bits : List ℕ) : Stmt :=
  let cap := D.visitCount
  let aux := (cap+1)*(cap+1)
  .seq (Prefix.initGen 0 cap) (.seq (sweep (stepBody cap aux id) D.blocks 0) (finishCount 0 aux cap bits))

/-- The actual repeated-box traversal and binary comparison implement the auxiliary relation. -/
theorem checker_tests (D : Directory) (id : ℕ) (bits : List ℕ) (e : List ℕ) :
    let cap := D.occurrences.length
    Profile.Tests (checker D id bits) e (Accept cap ((cap+1)*(cap+1)) bits id D) := by
  unfold checker
  rw [D.visitCount_eq]
  apply Prefix.checks_congr (Prefix.seq_checks (Prefix.initGen_checks 0 _ e)
    (Prefix.seq_checks (steps_checks D _ _ id e) (finishCount_checks 0 _ _ bits e)))
  intro b
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, Accept, Prefix.Valid, matchAt, and_assoc]

/-- The guessed scratch rectangle is local to one subtotal check. -/
def row (D : Directory) (id : ℕ) (bits : List ℕ) : Stmt :=
  localFlags ((D.visitCount+1)*(D.visitCount+1)) (checker D id bits)

/-- No multiplicative factor is introduced by the auxiliary flags, even in a
sum with arbitrary following guards, signs, and guesses. -/
theorem row_checks (D : Directory) (id : ℕ) (bits : List ℕ) (e : List ℕ) :
    Profile.Tests (row D id bits) e (fun b => word b bits = (D.occurrences.map (selected id b)).count true) := by
  unfold row
  rw [D.visitCount_eq]
  apply localFlags_checks _ _ _ _ _ (checker_tests D id bits e)
  · intro v x h
    exact ((accept_stack_iff D id bits v x).mp h).1
  · intro v h
    refine ⟨canonicalAux D id (lookup v), (accept_stack_iff D id bits v _).mpr ⟨h,rfl⟩, ?_⟩
    intro x hx
    exact ((accept_stack_iff D id bits v x).mp hx).2

end Gadget

/-- Reuse the original wire assignment for every reported gadget position. -/
def Directory.subtotalGuards (D : Directory) : Stmt :=
  sequence (D.reportedCounts.zipIdx.map fun z => Gadget.row D z.2 z.1)

private theorem map_count_true {α : Type*} (xs : List α) (p : α → Bool) :
    (xs.map p).count true = xs.countP p := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases h : p a <;> simp [h, ih]

/-- Every announced count equals the number of actually selected positions. -/
theorem Directory.subtotalGuards_checks (D : Directory) (e : List ℕ) :
    Profile.Tests D.subtotalGuards e (fun b => ∀ a : Fin D.reportedCounts.length,
      D.occurrences.countP (selected a.val b) = word b D.reportedCounts[a]) := by
  apply Prefix.checks_congr (sequence_checks D.reportedCounts.zipIdx
    (fun z => Gadget.row D z.2 z.1) e (fun z b => decide (word b z.1 = (D.occurrences.map (selected z.2 b)).count true))
    (fun z _ => Prefix.checks_congr (Gadget.row_checks D z.2 z.1 e) (fun _ => by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq])))
  intro b
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, decide_eq_true_eq, map_count_true]
  constructor
  · intro h a
    have hm : (D.reportedCounts[a],a.val) ∈ D.reportedCounts.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem a.isLt)
    exact (h _ hm).symm
  · intro h z hz
    have he := List.mem_zipIdx_iff_getElem?.mp hz
    have hi : z.2 < D.reportedCounts.length := by
      by_contra! hf
      simp [List.getElem?_eq_none_iff.mpr hf] at he
    have hfield := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans he)
    simpa [← hfield] using (h ⟨z.2,hi⟩).symm

end CellSparse

end BorderVNP
end Computability
end OAI
