import OAI.Computability.BorderVNP.RoutingISASignedPrepReportRows
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

/-! # Physically prepared report assignments before private cell dispatch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyCellReports BorderVNP.Cube

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)

/-- All real local continuations from the just-returned owned-group state. -/
abbrev LocalTail (s : Bank w) (m : Memory w) :=
  Σ d : Returns controls pub mac s m,
    Σ r : Returns prepareCellReports pub mac d.val.2.1 d.val.2.2, Returns arguments pub mac r.val.2.1 r.val.2.2

private theorem deterministic_eq {c : Code} {s m} (det : c.deterministic=true)
    (x y : Returns c pub mac s m) : x=y := by
  obtain ⟨ev,reg,mem⟩ := x.property.unique_of_deterministic det y.property
  exact Subtype.ext (Prod.ext ev (Prod.ext reg mem))

/-- Reindex the real continuation by the per-cell physical report assignments. A
report is retained precisely when the actual compact task serializer returns at
its own post-report state. Every such state and every chronological bit is kept. -/
noncomputable def checkedReportTailEquiv {s : Bank w} {m : Memory w} (d : Returns controls pub mac s m)
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {description : ℕ}
    (seed : PreparedReportInput pub d.val.2.2 cs q description) :
    let report := assignedReportReturnEquiv seed mac d.val.2.1
    LocalTail pub mac s m ≃ {rows : ReportAssignments cs //
      Nonempty (Returns arguments pub mac (report rows).val.2.1 (report rows).val.2.2)} := by
  intro report
  let localAt (y : Returns controls pub mac s m) :=
    Σ r : Returns prepareCellReports pub mac y.val.2.1 y.val.2.2, Returns arguments pub mac r.val.2.1 r.val.2.2
  let once : localAt d ≃ LocalTail pub mac s m := Equiv.ofBijective (Sigma.mk d) ⟨
    fun _ _ e => eq_of_heq (Sigma.mk.inj e).2,
    fun ⟨d',t⟩ => by
      obtain rfl := deterministic_eq pub mac (by decide) d d'
      exact ⟨t,rfl⟩⟩
  let chooseArgs : (Σ rows : ReportAssignments cs, Returns arguments pub mac (report rows).val.2.1 (report rows).val.2.2) ≃
      {rows : ReportAssignments cs // Nonempty (Returns arguments pub mac (report rows).val.2.1 (report rows).val.2.2)} :=
    { toFun x := ⟨x.1,⟨x.2⟩⟩
      invFun x := ⟨x.val,x.property.some⟩
      left_inv := fun ⟨r,a⟩ => congrArg (Sigma.mk r) (deterministic_eq pub mac (by decide) _ a)
      right_inv _ := rfl }
  exact once.symm.trans ((Equiv.sigmaCongrLeft' report.symm).trans chooseArgs)

/-- If the concrete post-report task buffers fit for every assignment, its physical
argument run closes the acceptance condition. This map retains every report once. -/
noncomputable def allReportTailEquiv {s : Bank w} {m : Memory w} (d : Returns controls pub mac s m)
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {description : ℕ}
    (seed : PreparedReportInput pub d.val.2.2 cs q description)
    (fitted : ∀ rows : ReportAssignments cs, let r := assignedReportReturnEquiv seed mac d.val.2.1 rows
      Nonempty (Returns arguments pub mac r.val.2.1 r.val.2.2)) :
    LocalTail pub mac s m ≃ ReportAssignments cs :=
  (checkedReportTailEquiv pub mac d seed).trans (Equiv.subtypeUnivEquiv fitted)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
