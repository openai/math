import OAI.Computability.BorderVNP.DiagonalPassingSeedSource
import OAI.Computability.BorderVNP.DiagonalReportBatchFiber

/-! # Read one original seed's report directly from the passing cell directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.AssignedCell

open Packing.BottomReports CellSparse
open scoped Classical
open private append_checked from OAI.Computability.BorderVNP.DiagonalCheckedCellReport

/-- The uniquely spelled canonical report on a passing local core really
passes its augmented directory. This uses the cell's saved guard and ordered
bottom bundles before the global tally check or the lead reader runs. -/
theorem Passing.canonical_augmented {l : ReportLayout} {s : AssignedCell l} {w order : ℕ}
    (h : s.Passing w order) (out : ReportCell l)
    (uses : (out.bundles.map ReportBundle.useCount).sum=(s.bundles.map Bundle.useBits).sum)
    (correct : out.bits=s.spelling) :
    (appendRows s.initial (supplements (s.pre.length+l.gadgets*l.countWidth) s.bundles)).guardedObservations
      (lookup (s.pre++out.bits)) = some s.observations := by
  have length : s.pre.length=s.privateWires+s.boundary.length := by simp [pre]
  let extra := supplements (s.pre.length+l.gadgets*l.countWidth) s.bundles
  let D := appendRows s.initial extra
  let raw := lookup (s.pre++out.bits)
  have weight := checked_report_weight out s.initial s.pre s.bundles s.observations h.unsigned (length ▸ h.layout)
    (h.seen _) h.core uses h.range h.fit
  have good : D.weight raw=1 := weight.trans (ite_eq_left correct)
  have unsigned : D.SignFree := h.unsigned
  rw [unsigned.weight_guarded] at good
  split at good
  · rename_i accepted
    obtain ⟨os,seen,_⟩ := accepted
    have old := ((append_checked extra (supplements_wiring _ _) raw os).mp seen).1
    have identified := Option.some.inj (old.symm.trans (h.seen _))
    exact seen.trans (congrArg some identified)
  · contradiction

end DiagonalTallyCellReports.AssignedCell

namespace Packing.DeckGrid.WiredWitness

open CellSparse BottomReports Inherited DiagonalTallyCellReports
open private append_checked from OAI.Computability.BorderVNP.DiagonalCheckedCellReport

/-- In a successful physical cell the copy's row tests belong to the actual
supplement at the cursor after the preceding report bundles. The report bits
are read directly after that cell's full private prefix and supply. -/
def SeedBirthReceipt.ofDirectory {copies base : ℕ} {layout : Slab} {birth : Site} {factors : List Factor}
    (report : ReportBundle) {l : ReportLayout} (out : ReportCell l) (before after : List ReportBundle)
    (parts : out.bundles=before++report::after) (pre : List Bool) (extent : pre.length=out.privateWires+out.supplied)
    (D : Directory) (previous rest : List Bundle) (source : Bundle)
    (header : source.header.boxBase=base ∧ source.header.orig=layout.orig ∧ source.header.cap=layout.capReport ∧
      source.header.copies=copies) (body : source.factors=factors)
    (prefixCount : (previous.map Bundle.useBits).sum=(before.map ReportBundle.useCount).sum)
    {obs : List (Bool × Option ℕ)}
    (accepted : (appendRows D (supplements (pre.length+l.gadgets*l.countWidth) (previous++source::rest))).guardedObservations
      (lookup (pre++out.bits))=some obs)
    (guess : Fin copies → Fin layout.guessed → Bool) (original : ℕ → Bool)
    (window : ∀ (i : Fin copies) (j : Fin layout.stride), lookup (pre++out.bits) (base+i.val*layout.stride+j.val)=
      original (i.val*layout.stride+j.val))
    (guesses : ∀ (i : Fin copies) (j : Fin layout.guessed), original (i.val*layout.stride+j.val)=guess i j)
    (seen : (birth.observe original).isSome=true) :
    SeedBirthReceipt copies base layout birth factors report (lookup (pre++out.bits)) guess l original := by
  refine ⟨D.boxes,out,before,after,parts,?_,window,guesses,seen,?_⟩
  · intro k hk
    rw [← extent]
    simp [lookup,List.head?_drop,hk]
  · have passed := ((append_checked _ (supplements_wiring _ _) _ _).mp accepted).2
    intro row hrow
    apply passed row
    rw [supplements_append,List.mem_append]
    right
    apply List.mem_append_left
    simpa only [nextCursor,extent,prefixCount,header.1,header.2.1,header.2.2.1,header.2.2.2,body] using hrow

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
