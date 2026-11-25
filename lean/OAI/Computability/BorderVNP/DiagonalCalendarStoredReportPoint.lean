import OAI.Computability.BorderVNP.DiagonalCalendarStoredOriginalReportFamily

/-! # Stored reports at individual original fields and teams

The site type below is the dependent codomain of `StoredReportsAtOriginalInputs`.
A pointwise existence proof supplies one stored family for all later uses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Command Term

set_option maxRecDepth 28000
set_option maxHeartbeats 22000000

private def defineStoredOperation (name : Name) (levelParams : List Name)
    (ty body : Expr) (doc : String) : TermElabM Unit := do
  let shared := ShareCommon.shareCommon' #[ty,body]
  addDecl <| .defnDecl {
    name := name
    levelParams := levelParams
    type := shared[0]!
    value := shared[1]!
    hints := .regular 0
    safety := .safe }
  addDocStringCore name doc

run_cmd liftTermElabM do
  let familyName := ``SignedCalendarAt.StoredReportsAtOriginalInputs
  let info ← getConstInfo familyName
  let levels := info.levelParams.map Level.param
  let family := Lean.mkConst familyName levels
  let pointName := `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.StoredReportPointOnOriginalInputs
  let pointBody ← forallTelescope info.type fun inputs _ => do
    let full := mkAppN family inputs
    forallBoundedTelescope full (some 2) (whnfType := true) fun whereAt result => do
      unless whereAt.size == 2 do throwError "the original stored family must take a field and a team"
      let some _ ← whnfUntil result ``PSigma | throwError "expected the reported source parameters"
      mkLambdaFVars (inputs ++ whereAt) result
  defineStoredOperation pointName info.levelParams (← inferType pointBody) pointBody
    "The stored report and its source parameters at this original calendar field and team."
  let site := Lean.mkConst pointName levels
  let (choiceType,choiceValue) ← forallTelescope info.type fun inputs _ => do
    let full := mkAppN family inputs
    let pointwise ← forallBoundedTelescope full (some 2) fun whereAt _ => do
      let point := mkAppN site (inputs ++ whereAt)
      mkForallFVars whereAt (mkApp (Lean.mkConst ``Nonempty [← getLevel point]) point)
    withLocalDeclD `recorded pointwise fun recorded => do
      let selected ← forallBoundedTelescope full (some 2) fun whereAt _ => do
        let point := mkAppN site (inputs ++ whereAt)
        let observed := mkAppN recorded whereAt
        mkLambdaFVars whereAt (mkAppN (Lean.mkConst ``Classical.choice [← getLevel point]) #[point,observed])
      let params := inputs.push recorded
      return (← mkForallFVars params full, ← mkLambdaFVars params selected)
  defineStoredOperation `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.storedReportsFromOriginalPoints
    info.levelParams choiceType choiceValue
    "Choose one stored report per original field and team from the supplied pointwise existence proof."

end Diagonal

end BorderVNP
end Computability
end OAI
