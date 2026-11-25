import OAI.Computability.BorderVNP.DiagonalPositiveReportWeights
import OAI.Computability.BorderVNP.DiagonalJointAcceptedTerms

/-! # The real positive private weight on all physically received report assignments -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.JoinedCells

open VPVNP.BurstRAM TeamContraction CompactMachine CellMacro.Generator DiagonalTallyCellReports CellSparse
open scoped Classical BigOperators

variable {T w n : ℕ} {gen : Fragment IO} {Prefix : Fin T → Type}
    {pub : Fin T → Arg → Word w} {mem : ∀ u, Prefix u → Memory w}
    {rows : ∀ u a, GeneratedCells gen n (pub u) (mem u a)} {pre : ∀ u, Prefix u}
    (J : JoinedCells pub mem rows pre) (z : J.Private)
    {layout : Fin T → ReportLayout} (ss : ∀ u, List (AssignedCell (layout u)))
    (r : ∀ u, ReportAssignments ((ss u).map AssignedCell.report))

/-- A physical bijection from all actual received owned rows to the joined
cell names, together with the contents supplied at each address. This is
only a comparison of typed directories and literal bits. -/
structure ReportImage where
  /-- Enumerate the cells in each physical report batch. -/
  number : (Σ u : Fin T, Fin (ss u).length) ≃ J.Cell
  directory : ∀ u i, (J.cells (number ⟨u,i⟩)).directory=((ss u).get i).augmented
  privateBits : ∀ u i, List.ofFn (z (number ⟨u,i⟩))=List.ofFn ((ss u).get i).assignment
  external : ∀ u i, (J.cells (number ⟨u,i⟩)).external=((ss u).get i).boundary++
    ((r u).val.get (Fin.cast (assignedRows_length (r u)).symm i)).bits

/-- Exact correspondence on an arbitrary received report, before the
shared subtotal check or the lead entry is evaluated. A malformed report
removes the term at its private native cell. -/
theorem privateWeight_reports (I : J.ReportImage z ss r) (ok : ∀ u s, s ∈ ss u → s.Passing w n) :
    J.privateWeight z ≠ 0 ↔ ∀ u, ∃ ts, BatchReturns w n (ss u) (r u).val ts := by
  have weight (u : Fin T) (i : Fin (ss u).length) :
      (J.cells (I.number ⟨u,i⟩)).directory.weight (lookup (List.ofFn (z (I.number ⟨u,i⟩))++
        (J.cells (I.number ⟨u,i⟩)).external))=
      ((ss u).get i).reportWeight ((r u).val.get (Fin.cast (assignedRows_length (r u)).symm i)) := by
    rw [I.directory,I.privateBits,I.external,← List.append_assoc]
    rfl
  unfold privateWeight
  rw [Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ,forall_const]
  constructor
  · intro h u
    apply (assignedRows_iff (ss u) (ok u) (r u)).mp
    intro i
    rw [← weight u i]
    exact h (I.number ⟨u,i⟩)
  · intro h c
    obtain ⟨⟨u,i⟩,rfl⟩ := I.number.surjective c
    rw [weight]
    exact (assignedRows_iff (ss u) (ok u) (r u)).mpr (h u) i

end RoutingISA.Evaluator.JoinedCells

end BorderVNP
end Computability
end OAI
