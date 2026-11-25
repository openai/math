import OAI.Computability.BorderVNP.DiagonalPositiveFinishTeam
import OAI.Computability.BorderVNP.DiagonalPositiveReportChoices
import OAI.Computability.BorderVNP.CubePhysicalFinishReceipt

/-! # The joint native fiber of report choices and the common subtotal field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open CellSparse FiniteDiagonal.CellTrace

variable {l : ReportLayout} {w order : ℕ}

/-- A successful signed private call on the physically delivered report has
unit integer weight. The proof uses the actual count-and-use checker on the
original private/core wire assignment. -/
theorem AssignedCell.return_weight_one (s : AssignedCell l) (h : s.Passing w order)
    (stream : ℕ → Bool) (offset : ℕ) (t : List Bool × Bool)
    (ret : s.Returns w order (s.report.withTape stream offset) t) :
    s.augmented.weight (lookup (s.pre++(s.report.withTape stream offset).bits)) = 1 := by
  let r := s.report.withTape stream offset
  obtain ⟨_,outcome⟩ := s.native w order h
  have spell := ((outcome stream offset t).mp ret).1
  have len : s.pre.length=s.privateWires+s.boundary.length := by simp [AssignedCell.pre]
  have weights := checked_report_weight r s.initial s.pre s.bundles s.observations h.unsigned (len ▸ h.layout)
    (h.seen r.bits) h.core (by simpa only [r,ReportCell.withTape,tapeBundles_useCount] using h.uses) h.range h.fit
  dsimp only at weights
  rw [len] at weights
  exact weights.trans (ite_eq_left spell)

end DiagonalTallyCellReports

namespace RoutingISA.Evaluator.PositiveClaimCandidate

open VPVNP.BurstRAM TeamContraction.JointHeader CompactMachine CellMacro.Generator _root_.OAI.Computability.BorderVNP.Cube
open DiagonalTallyCellReports CellSparse
open scoped Classical

variable {axes box lanes selectors symbols w T n reserve groups cap dim width : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    {p : PositiveFields reserve axes groups cap T dim width}
    (X : PositiveClaimCandidate id gen n w p)

/-- Source-level identification of one canonical prepared cell with its native
checker. The original private digits, delivered data and report bits are all
compared with the genuine positive prefix's bank. -/
structure CellSource (X : PositiveClaimCandidate id gen n w p)
    (c : (X.joined X.canonical (X.candidate X.canonical).1).Cell) where
  /-- Public dimensions and addresses of the original cell report. -/
  layout : ReportLayout
  /-- The directory and original core assignment before reports. -/
  assigned : AssignedCell layout
  /-- The native count-and-use choice stream. -/
  stream : ℕ → Bool
  /-- The cursor at this cell in its team’s report stream. -/
  offset : ℕ
  /-- The native auxiliary choice tape and terminal sign. -/
  residual : List Bool × Bool
  passing : assigned.Passing w n
  returned : assigned.Returns w n (assigned.report.withTape stream offset) residual
  directory : ((X.joined X.canonical (X.candidate X.canonical).1).cells c).directory=assigned.augmented
  privateBits : List.ofFn ((X.candidate X.canonical).2 c)=List.ofFn assigned.assignment
  external : ((X.joined X.canonical (X.candidate X.canonical).1).cells c).external=
    assigned.boundary++(assigned.report.withTape stream offset).bits

/-- The canonical private weight follows from the actual passing cell packets.
Neither a nonzero subtotal result nor any field value is assumed. -/
theorem canonicalCellWeight_one (sources : ∀ c, CellSource X c) : X.canonicalCellWeight = 1 := by
  apply Finset.prod_eq_one
  intro c _
  let H := sources c
  rw [H.directory,H.privateBits,H.external,← List.append_assoc]
  exact H.assigned.return_weight_one H.passing H.stream H.offset H.residual H.returned

variable {Source : Type*} (layout : Source → Fin T → ReportLayout)
    (ss : ∀ a u, List (AssignedCell (layout a u)))
    (pass : ∀ a u v, v ∈ ss a u → v.Passing w n)
    (candidate : ∀ a, ((u : Fin T) → ReportChoice w n (ss a u)) → PositiveClaimCandidate id gen n w p)
    (source : ∀ a z c, CellSource (candidate a z) c)

/-- At fixed routed, original private data, eliminate the actual report
assignments and residual choices of every team together with the shared claim.
The inverse reconstructs the one canonical family of true positive histories. -/
noncomputable def reportClaimEquiv :
    (Σ a : Source, Σ z : (u : Fin T) → ReportChoice w n (ss a u),
      {raw : Fin (T*dim*width) → Bool // let X := candidate a z
        positivePass (X.team raw) (X.joined raw) (X.candidate raw)}) ≃ Source := by
  let reports (a : Source) := fun u : Fin T => (reportChoice_unique (ss a u) (pass a u)).choose
  have ok (a : Source) (z : (u : Fin T) → ReportChoice w n (ss a u)) : (candidate a z).canonicalCellWeight ≠ 0 := by
    rw [(candidate a z).canonicalCellWeight_one (source a z)]
    decide
  refine { toFun := Sigma.fst
           invFun := fun a => ⟨a,reports a,(candidate a (reports a)).canonical,
             ((candidate a (reports a)).pass_iff (ok a _) _).mpr rfl⟩
           left_inv := ?_
           right_inv := fun _ => rfl }
  rintro ⟨a,z,raw,h⟩
  have same : z=reports a := funext fun u => (reportChoice_unique (ss a u) (pass a u)).choose_spec.2.2 (z u)
  subst z
  apply congrArg (Sigma.mk a)
  apply congrArg (Sigma.mk (reports a))
  exact Subtype.ext (((candidate a (reports a)).pass_iff (ok a _) _).mp h).symm

end RoutingISA.Evaluator.PositiveClaimCandidate

end BorderVNP
end Computability
end OAI
