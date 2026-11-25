import Mathlib.Lean.Expr.Basic
import Lean

/-! # The source parameters carried by an original funded report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.SignedCalendarAt

open Lean Meta Elab Term

/-- Form a dependent package for the original source parameters of a funded
report. The supplied site parameters stay fixed at their physical values.
The last field is the original report's entire certified subtype. -/
partial def originalStoredReportTypeAt (pointType : Expr) (fixed : Array (Name × Expr)) : MetaM Expr := do
  let .forallE name ty body bi ← whnf pointType | throwError "missing the original funded report"
  let key := name.eraseMacroScopes
  if key == `original then
    unless (← whnfUntil ty ``Subtype).isSome do throwError "expected the certified funded report"
    return ty
  if let some (_, value) := fixed.find? (fun arg => arg.1 == key) then
    return ← originalStoredReportTypeAt (body.instantiate1 value) fixed
  unless #[`E,`I,`P,`iP,`bank,`fit,`cells,`emission,`Seed,`seed,`native].contains key || bi.isInstImplicit do
    throwError "unexpected unbundled report operand {name}"
  withLocalDecl name bi ty fun x => do
    let rest ← originalStoredReportTypeAt (body.instantiate1 x) fixed
    let fibre ← mkLambdaFVars #[x] rest
    return mkApp2 (mkConst ``PSigma [← getLevel ty, ← getLevel rest]) ty fibre

/-- Extract the original `Subtype` from its dependent package of source
parameters. This projection retains the supplied report itself. -/
partial def storedReportAtOriginalSite (x : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType x)
  if ty.isAppOf ``Subtype then return x
  unless ty.isAppOf ``PSigma do throwError "expected the stored field and its funded report"
  storedReportAtOriginalSite (mkProj ``PSigma 1 x)

/-- The certified original report at a single registered site. -/
elab "storedOriginalReportAt%" point:term:max : term => do
  storedReportAtOriginalSite (← elabTerm point none)

end Diagonal.SignedCalendarAt

end BorderVNP
end Computability
end OAI
