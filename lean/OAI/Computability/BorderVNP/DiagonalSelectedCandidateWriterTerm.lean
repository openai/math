import OAI.Computability.BorderVNP.DiagonalSelectedCandidateWriterLookup

/-! # Applying the selected writer lookup to a concrete physical site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term RoutingISA.Evaluator.SignedPrep

private def appliedParameters (e : Expr) (head : Name) : MetaM (Expr × NameMap Expr) := do
  let some app ← whnfUntil e head | throwError "expected {head} in the selected signed site"
  let info ← getConstInfo head
  let args := app.getAppArgs
  forallTelescope info.type fun binders _ => do
    let mut values : NameMap Expr := {}
    for binder in binders, arg in args do
      values := values.insert (← binder.fvarId!.getUserName) arg
    return (app, values)

private def parameter (args : NameMap Expr) (name : Name) : MetaM Expr := do
  let some value := args.find? name | throwError "missing parameter {name} in the selected signed site"
  return value

/-- Elaborate an application of the proved physical selection operation using the
parameter types of the original site. The result term is checked by the kernel. -/
elab "selectedCandidateWriterLookup%" task:term:max word:term:max label:term:max evidence:term:max result:term:max : term => do
  let task ← elabTerm task none
  let word ← elabTerm word none
  let label ← elabTerm label none
  let evidence ← elabTerm evidence none
  let result ← elabTerm result none
  forallBoundedTelescope (← inferType evidence) (some 3) fun binders _ => do
    unless binders.size == 3 do throwError "expected an exterior, a team and the reached signed site"
    let x := binders[0]!
    let u := binders[1]!
    let (siteApp, site) ← appliedParameters (← inferType binders[2]!) ``CandidateSite
    let (_, exterior) ← appliedParameters (← inferType x) ``HeaderExterior
    let (_, fields) ← appliedParameters (← parameter site `fields) ``Wiring.processorFields
    let (_, pins) ← appliedParameters (← parameter site `pins) ``Wiring.pinLayout
    let (_, transfer) ← appliedParameters (← parameter site `f) ``Wiring.transferFrame
    let mut args := site
    for name in [`R,`r,`t,`d,`link,`inner,`n,`Edge,`G,`pin] do
      args := args.insert name (← parameter fields name)
    args := args.insert `skeleton (← parameter exterior `L)
    args := args.insert `header (← parameter exterior `header)
    args := args.insert `volume (← parameter site `X)
    args := args.insert `dim (← parameter site `D₀)
    for (name, source) in [(`ib,`ibase),(`hb,`hbase),(`sb,`starbase)] do
      args := args.insert name (← mkLambdaFVars #[u] (← parameter pins source))
    args := args.insert `dst (← mkLambdaFVars #[u] (← parameter transfer `dst))
    args := args.insert `guess (← mkLambdaFVars #[u] (← parameter site `guess))
    for name in [`pub,`mac,`reg,`mem] do
      args := args.insert name (← mkLambdaFVars #[x,u] (← parameter site name))
    args := args.insert `task task |>.insert `word word |>.insert `label label
      |>.insert `evidence evidence |>.insert `result result
    let operation ← getConstInfo ``selectedLookupOfCandidateWriters
    let fn := Lean.mkConst operation.name siteApp.getAppFn.constLevels!
    forallTelescope operation.type fun params _ => do
      let actual ← params.mapM fun param => do
        let name ← param.fvarId!.getUserName
        if let some value := args.find? name then return value
        -- Instances for the site inventory and received row indices.
        let ty ← inferType param
        unless ty.isAppOf ``Fintype do throwError "missing selection argument {name}"
        let index ← ty.appArg!.fvarId!.getUserName
        if index == `I then
          -- CandidateSite carries the very instance used to enumerate its hosts.
          return siteApp.getAppArgs[22]!
        let α ← parameter site index
        synthInstance (mkApp (Lean.mkConst ``Fintype [← getDecLevel α]) α)
      return mkAppN fn actual

end TeamContraction

end BorderVNP
end Computability
end OAI
