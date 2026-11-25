import OAI.Computability.BorderVNP.DiagonalPositiveOwnedReports
import OAI.Computability.BorderVNP.DiagonalNativeCorePaths
import OAI.Computability.BorderVNP.PackedFinalAssignedReport

/-! # Failed genuine original guards exclude every physical report and private return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.AssignedCell

open CellSparse FiniteDiagonal.CellTrace

variable {l : ReportLayout} (s : AssignedCell l)

/-- A failed original guard gives zero integer weight for every reported
count and use field on the same original core. -/
theorem reportWeight_zero (unsigned : s.initial.SignFree)
    (bad : ∀ tail,s.initial.guardedObservations (lookup (s.pre++tail))=none) (r : ReportCell l) :
    s.reportWeight r=0 := by
  have len : s.pre.length=s.privateWires+s.boundary.length := by simp [pre]
  have h := checked_report_absent r s.initial s.pre s.bundles unsigned (bad r.bits)
  dsimp only at h
  rw [len] at h
  exact h

/-- No individual positive or negative return of the real clocked private
macro is possible on a failed original guard, even on an arbitrary report. -/
theorem no_return {w n : ℕ} (unsigned : s.initial.SignFree)
    (bad : ∀ tail,s.initial.guardedObservations (lookup (s.pre++tail))=none)
    (hw : 0<w) (profile : s.initial.ProfileWidths)
    (clock : ∀ x : Fin s.report.tailWidth → Bool,Copied.FitsClock s.augmented w n s.privateWires (s.boundary++List.ofFn x))
    (r : ReportCell l) (len : r.bits.length=s.report.tailWidth) (residual : List Bool × Bool) :
    ¬ s.Returns w n r residual := by
  let x := fun i : Fin s.report.tailWidth => r.bits.get (Fin.cast len.symm i)
  have eq : List.ofFn x=r.bits := by
    apply List.ext_getElem (List.length_ofFn.trans len.symm)
    intro j hj hj'
    simp [x]
  have absent := fixed_native_absent s.report s.initial s.assignment s.boundary s.bundles unsigned bad hw profile clock
  have run := absent x residual.1 residual.2
  simpa only [eq,Returns,augmented] using run

end DiagonalTallyCellReports.AssignedCell

namespace Packing.Inherited.FinalCell

open Crossing CellAddresses CellSparse

variable {D M np ns C : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (c : Fin C) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M)
    (portID : P ↪ Fin np) (owner : Fin ns → ℕ) (state : Site.Programs N)

local notation3 "key" => (fun v => (cell v).val)
local notation3 "progs" => (fun v => (state v).program)
local notation3 "size" => (fun v => (state v).program.size)

/-- The original finite core guard and the genuine native owner-numbered
directory give the same result on every trailing report spelling. -/
theorem finite_guarded_tail (reports : List (List ℕ)) (ho : ∀ v,owner (siteID v)=(cell v).val)
    (hin : ∀ v,(state v).program.incoming=incoming N v) (schema : ∀ v,(state v).program.Schema)
    (locality : ∀ v,(state v).program.Local) (relative : ∀ v,(state v).program.RelativeBoxes)
    (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c size) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) (tail : List Bool) :
    let D := directory owner N key siteID edgeID portID progs c.val reports
    let pre := bank N cell c size g a x
    D.guardedObservations (lookup (pre++tail))=D.guardedObservations (lookup pre) := by
  let widths := FinalReports.bank_sizes N cell progs c
  let gn := g ∘ Fin.cast widths.1
  let an := a ∘ Fin.cast widths.2.1
  let xn := x ∘ Fin.cast widths.2.2
  have eq := FinalTies.bank_nat N cell c progs g a x
  change bank N key c.val size gn an xn=bank N cell c size g a x at eq
  have same := guarded_tail N key c.val siteID edgeID portID owner progs reports ho hin schema locality relative gn an xn tail
  change (directory ..).guardedObservations (lookup (bank N key c.val size gn an xn++tail))=
    (directory ..).guardedObservations (lookup (bank N key c.val size gn an xn)) at same
  simpa only [eq] using same

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
