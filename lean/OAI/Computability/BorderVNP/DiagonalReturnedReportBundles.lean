import OAI.Computability.BorderVNP.DiagonalReportBatchFiber
import OAI.Computability.BorderVNP.PackedBottomReportBundle

/-! # Exact chronological source bundles of a returned physical cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open Packing.BottomReports CellSparse
open scoped Classical

/-- Each source's restored selected-wire reads, in its original occurrence and
copy order, are exactly the bits prescribed by its private input prefix. -/
theorem physicalBundle_choiceList (b : Bundle) (body : List Factor) (pre : List Bool) :
    List.ofFn (physicalBundle b.header body b.factors (lookup pre)).uses = List.ofFn (b.useChoice pre) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,physicalBundle,positions_length,Bundle.useBits]
    exact (List.length_ofFn (f := b.useChoice pre)).symm
  · intro i h₁ h₂
    simp only [List.getElem_ofFn]
    rfl

private theorem tapeBundles_choices {I : Type} (bs : I → Bundle) (body : I → List Factor)
    (old : I → ℕ → Bool) (pre : List Bool) (tape : ℕ → Bool) (rows : List I) (p : ℕ)
    (correct : (tapeBundles tape p (rows.map fun j => physicalBundle (bs j).header (body j) (bs j).factors
        (old j))).flatMap (fun b => List.ofFn b.uses) = useTape pre (rows.map bs)) :
    tapeBundles tape p (rows.map fun j => physicalBundle (bs j).header (body j) (bs j).factors (old j)) =
      rows.map fun j => physicalBundle (bs j).header (body j) (bs j).factors (lookup pre) := by
  induction rows generalizing p with
  | nil => rfl
  | cons j tail ih =>
    let make := physicalBundle (bs j).header (body j) (bs j).factors
    let first := (make (old j)).withTape tape p
    have parts := List.append_inj
      (show List.ofFn first.uses ++ _ = List.ofFn ((bs j).useChoice pre) ++ _ from correct)
      (by
        simp only [first,make,ReportBundle.withTape,List.length_ofFn,physicalBundle,positions_length,Bundle.useBits]
        exact (List.length_ofFn (f := (bs j).useChoice pre)).symm)
    have bits := List.ofFn_injective (parts.1.trans (physicalBundle_choiceList (bs j) (body j) pre).symm)
    have head : first=make (lookup pre) := congrArg
      (ReportBundle.mk (bs j).header (body j) (positions (bs j).header.orig (bs j).factors)) bits
    exact congrArg₂ List.cons head (ih _ parts.2)

/-- An actual passing native return makes every source bundle of this cell
equal to its physical bundle on the retained private bits: immutable header,
one-copy body, marked positions, and every guessed use bit. -/
theorem AssignedCell.returned_bundles {l : ReportLayout} (s : AssignedCell l) {w n : ℕ} (pass : s.Passing w n)
    {I : Type} (rows : List I) (bs : I → Bundle) (body : I → List Factor) (old : I → ℕ → Bool)
    (inventory : s.bundles = rows.map bs)
    (stored : s.report.bundles=rows.map fun j => physicalBundle (bs j).header (body j) (bs j).factors (old j))
    (tape : ℕ → Bool) (p : ℕ) (ret : List Bool × Bool)
    (returns : s.Returns w n (s.report.withTape tape p) ret) :
    (s.report.withTape tape p).bundles =
      rows.map (fun j => physicalBundle (bs j).header (body j) (bs j).factors (lookup s.pre)) := by
  obtain ⟨_,classify⟩ := s.native w n pass
  let row := s.report.withTape tape p
  have spell := ((classify tape p ret).mp returns).1
  have split := List.append_inj (show countPart row.counts ++ row.bundles.flatMap (fun b => List.ofFn b.uses) =
      countPart (observationCounts s.observations l.gadgets l.countWidth) ++ useTape s.pre s.bundles from spell)
    (by simp only [countPart_length])
  have chosen := split.2
  rw [inventory] at chosen
  change tapeBundles tape (p+l.gadgets*l.countWidth) s.report.bundles=_
  rw [stored]
  apply tapeBundles_choices bs body old s.pre tape rows _
  simpa only [row,ReportCell.withTape,stored] using chosen

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
