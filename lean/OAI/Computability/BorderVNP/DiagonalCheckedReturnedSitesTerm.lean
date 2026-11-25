import OAI.Computability.BorderVNP.DiagonalPinnedRouteReadback

/-! # Recovering the native decoder operands from returned pinned builders -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CalendarReturnedSiteElab

open Lean Elab Term Meta

private def headed (expression : Expr) (head : Name) : MetaM Expr := do
  let some result ← whnfUntil expression head | throwError "expected {head} in returned builder"
  pure result

/-- Recover the two families occurring in the original returned witness,
with the same raw header, layout, extent, frame and builder binders. -/
private def returnedFamilies (source : Expr) : MetaM (Expr × Expr × Level) := do
  forallBoundedTelescope (← inferType source) (some 2) (whnfType := true) fun header claim => do
    unless header.size == 2 do throwError "expected a raw header and its admission"
    let rec collect (now : Expr) (binders : Array Expr) : List Name → MetaM (Expr × Expr × Level)
      | nm :: rest => do
        let quant ← headed now ``Exists
        withLocalDeclD nm quant.getAppArgs[0]! fun binder =>
          collect (mkApp quant.getAppArgs[1]! binder) (binders.push binder) rest
      | [] => do
        let sourceFacts ← headed now ``And
        let reports ← headed sourceFacts.getAppArgs[1]! ``And
        let result ← headed reports.getAppArgs[1]! ``Exists
        let siteType := result.getAppArgs[0]!
        if siteType.containsFVar (binders[3]!.fvarId!) then
          throwError "site type depends on a builder"
        let sites ← mkLambdaFVars (header ++ binders.extract 0 3) siteType
        let property ← mkLambdaFVars (header ++ binders) result.getAppArgs[1]!
        return (sites, property, result.getAppFn.constLevels!.head!)
    collect claim #[] [`wire,`extent,`physicalFrame,`builder]

/-- Reuse the arguments already present in the recorded decoder instead of
resolving its large dependently typed arena and programs a second time. -/
private def decoderInputs (route : Expr) : MetaM (NameMap Expr) := do
  forallBoundedTelescope (← inferType route) (some 2) (whnfType := true) fun bs result => do
    unless bs.size == 2 do throwError "the decoder does not take the returned frames and checks"
    let dom ← headed (← inferType bs[0]!) ``TeamContraction.AdmittedPinnedFrames
    let info ← getConstInfo ``TeamContraction.AdmittedPinnedFrames
    let mut supplied ← forallBoundedTelescope info.type (some dom.getAppNumArgs) fun formals _ => do
      let mut map : NameMap Expr := {}
      for binder in formals, value in dom.getAppArgs do
        map := map.insert (← binder.fvarId!.getUserName) value
      pure map
    supplied := supplied.insert `Passed (← inferType bs[1]!)
    if !bs.any (fun x => result.containsFVar x.fvarId!) then
      supplied := supplied.insert `Result result
    return supplied

/-- Assemble only the arguments recorded in the real route and chosen source. The
kernel checks the resulting ordinary application when it is used as a term. -/
private def positional (route real checks : Expr) : MetaM Expr := do
  let (sites, property, siteSort) ← returnedFamilies real
  let supplied : NameMap Expr := (← decoderInputs route) |>.insert `route route |>.insert `Publication sites
    |>.insert `K property |>.insert `real real |>.insert `checks checks
  let info ← getConstInfo ``TeamContraction.checkedReadbackOfPinnedBuilders
  let fn ← mkConstWithFreshMVarLevels info.name
  let mut ty := info.instantiateTypeLevelParams fn.constLevels!
  let mut args := #[]
  while ty.isForall do
    let .forallE name domain body _ := ty | unreachable!
    let some v := supplied.find? name | throwError "decoder missing formal parameter {name}"
    if name == `Result || name == `Publication then
      let .sort level := domain.getForallBody | throwError "unexpected universe binder {name}"
      let actual ← if name == `Result then getLevel v else pure siteSort
      unless ← isLevelDefEq level actual do
        throwError "universe mismatch on {name}: {level} versus {actual}"
    args := args.push v
    ty := body
  let fn ← instantiateMVars fn
  return mkAppN fn args

/-- Apply the checked readback theorem to the route, its returned sites and its header checks. -/
elab "checkedReturnedSites% " dec:term "," src:term "," chk:term : term => do
  let route ← elabTerm dec none
  let real ← elabTerm src none
  let checks ← elabTerm chk none
  synthesizeSyntheticMVarsNoPostponing
  positional route real checks

end Diagonal.CalendarReturnedSiteElab

end BorderVNP
end Computability
end OAI
