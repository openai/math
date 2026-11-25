import OAI.Computability.BorderVNP.DiagonalPositiveReportChoices
import Mathlib.Data.List.Forall2

/-! # Recovering the accepted report choices from unscreened physical cell weights -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open CellSparse FiniteDiagonal.CellTrace
open scoped Classical

variable {l : ReportLayout} {w order : ℕ}

/-- Integer weight of the actual guessed private bank and the delivered report
on its original cell. -/
noncomputable def AssignedCell.reportWeight (s : AssignedCell l) (r : ReportCell l) : ℤ :=
  s.augmented.weight (lookup (s.pre++r.bits))

/-- The true sign-free checker is nonzero on an arbitrary stream exactly when
there is a genuine native residual choice for that stream. -/
theorem AssignedCell.nonzero_iff_returns (s : AssignedCell l) (h : s.Passing w order)
    (a : ℕ → Bool) (p : ℕ) :
    s.reportWeight (s.report.withTape a p) ≠ 0 ↔ ∃ t,s.Returns w order (s.report.withTape a p) t := by
  let r := s.report.withTape a p
  obtain ⟨u,result⟩ := s.native w order h
  have len : s.pre.length=s.privateWires+s.boundary.length := by simp [AssignedCell.pre]
  have weight := checked_report_weight r s.initial s.pre s.bundles s.observations h.unsigned (len ▸ h.layout)
    (h.seen r.bits) h.core (by simpa only [r,ReportCell.withTape,tapeBundles_useCount] using h.uses) h.range h.fit
  dsimp only at weight
  rw [len] at weight
  change s.augmented.weight (lookup (s.pre++r.bits)) ≠ 0 ↔ _
  change s.augmented.weight (lookup (s.pre++r.bits)) = (if r.bits=s.spelling then 1 else 0) at weight
  rw [weight]
  by_cases same : r.bits=s.spelling
  · refine ⟨fun _ => ⟨(u,false),(result a p _).mpr ⟨same,rfl⟩⟩,fun _ => ?_⟩
    rw [ite_eq_left same]
    decide
  · constructor
    · intro nonzero
      exact (nonzero (ite_eq_right same)).elim
    · rintro ⟨t,ret⟩
      exact (same ((result a p t).mp ret).1).elim

private theorem tapeRows_iff (ss : List (AssignedCell l)) (ok : ∀ s ∈ ss,s.Passing w order)
    (a : ℕ → Bool) (p : ℕ) :
    let rows := tapeCells a p (ss.map AssignedCell.report)
    List.Forall₂ (fun s r => s.reportWeight r ≠ 0) ss rows ↔ ∃ ts, BatchReturns w order ss rows ts := by
  induction ss generalizing p with
  | nil => exact ⟨fun _ => ⟨[],trivial⟩,fun _ => .nil⟩
  | cons s ss ih =>
    let r := s.report.withTape a p
    let tail := tapeCells a (p+s.report.tailWidth) (ss.map AssignedCell.report)
    have check := s.nonzero_iff_returns (ok s List.mem_cons_self) a p
    have rest := ih (fun v hv => ok v (.tail s hv)) (p+s.report.tailWidth)
    change List.Forall₂ _ (s::ss) (r::tail) ↔ ∃ ts, BatchReturns w order (s::ss) (r::tail) ts
    constructor
    · intro pair
      obtain ⟨hv,ht⟩ := List.forall₂_cons.mp pair
      obtain ⟨t,rt⟩ := check.mp hv
      obtain ⟨ts,rs⟩ := rest.mp ht
      exact ⟨t::ts,rt,rs⟩
    · rintro ⟨_ | ⟨t,ts⟩,h⟩
      · exact h.elim
      · exact .cons (check.mpr ⟨t,h.1⟩) (rest.mpr ⟨ts,h.2⟩)

/-- An arbitrary physical report assignment has the frozen number of rows. -/
theorem assignedRows_length {ss : List (AssignedCell l)} (r : ReportAssignments (ss.map AssignedCell.report)) :
    r.val.length=ss.length := by
  have same := congrArg List.length r.property
  simpa only [eraseReportBits,tapeCells_length,List.length_map] using same

/-- Unscreened received report fields pass on their owned cell weights if
and only if actual native choices exist for every cell. -/
theorem assignedRows_iff (ss : List (AssignedCell l)) (ok : ∀ s ∈ ss,s.Passing w order)
    (r : ReportAssignments (ss.map AssignedCell.report)) :
    (∀ i : Fin ss.length, (ss.get i).reportWeight (r.val.get (Fin.cast (assignedRows_length r).symm i)) ≠ 0) ↔
      ∃ ts, BatchReturns w order ss r.val ts := by
  let tape := (reportAssignmentEquiv (ss.map AssignedCell.report)).symm r
  have rows : cellsOfTape (ss.map AssignedCell.report) tape = r.val :=
    congrArg Subtype.val ((reportAssignmentEquiv (ss.map AssignedCell.report)).apply_symm_apply r)
  have same := tapeRows_iff ss ok (fun i => if h : i<(reportBits (ss.map AssignedCell.report)).length then tape ⟨i,h⟩ else false) 0
  change List.Forall₂ _ ss (cellsOfTape _ tape) ↔ ∃ ts,BatchReturns w order ss (cellsOfTape _ tape) ts at same
  rw [rows,List.forall₂_iff_get] at same
  constructor
  · intro h
    exact same.mp ⟨(assignedRows_length r).symm,fun i hi _ => h ⟨i,hi⟩⟩
  · intro h i
    exact (same.mpr h).2 i.val i.isLt (i.isLt.trans_eq (assignedRows_length r).symm)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
