import OAI.Computability.BorderVNP.DiagonalOriginalStoredReportContext

/-! # Mark bounds on the actual rows of a stored original report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.SignedCalendarAt

open Lean Meta

private partial def markedOperand (type : Expr) : MetaM Expr := do
  let .forallE name domain rest info ← whnf type |
    throwError "the original report payer has no mark bound"
  if name.eraseMacroScopes == `marked then return domain
  withLocalDecl name info domain fun x => markedOperand (rest.instantiate1 x)

private def sourceRowsIn (target : Expr) : MetaM (Array Expr) :=
  forallBoundedTelescope target (some 2) fun row _ => do
    unless row.size == 2 do throwError "expected an original row and its membership"
    let membership ← inferType row[1]!
    let some source := membership.getAppArgs.find? (fun x =>
        x.getAppFn.constName? == some ``DiagonalTallyCellReports.ReportDirectory.sourceCells) |
      throwError "the payer does not refer to the original report's source cells"
    return source.getAppArgs

private def originalReportMarkBounds : MetaM Expr :=
  withStoredReportOnOriginalInputs fun point => do
    let target ← markedOperand point.payerType
    let rows ← sourceRowsIn target
    -- The owner's memory, like the layout, comes from the payer. Its read bank
    -- is the output of the sparse emission saved in this same report.
    let #[_, cells, layout, home, payload, team, owner, external, supply, widths, digits] := rows |
      throwError "incomplete original report directory"
    withLocalDeclD `bank point.bankType fun bank => do
      let useMarks := mkAppN point.markBounds
        #[bank,cells,layout,home,team,owner,external,supply,widths,digits,payload]
      let .forallE name domain _ info ← whnf (← inferType useMarks) |
        throwError "expected the saved equality of the original payload"
      withLocalDecl name info domain fun saved => do
        mkLambdaFVars #[bank,saved] (mkExpectedPropHint (mkApp useMarks saved) target)

open Lean.Elab.Term in
local elab "originalReportMarkBounds%" : term => originalReportMarkBounds

private def savedMarkBound {P : Prop} (h : P) : PSigma (fun p : Prop => p) := ⟨P,h⟩

private noncomputable def markBoundAtOriginalReport : PSigma (fun p : Prop => p) :=
  savedMarkBound originalReportMarkBounds%

/-- For every original field and team, the saved equality of its report payload
bounds each retained mark's parameter by the word capacity and its position
by the word width, on the exact rows used by the payer. -/
theorem paidMarkBoundsAtOriginalInputs : markBoundAtOriginalReport.1 := markBoundAtOriginalReport.2

end Diagonal.SignedCalendarAt

end BorderVNP
end Computability
end OAI
