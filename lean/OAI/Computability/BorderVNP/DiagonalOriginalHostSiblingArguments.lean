import OAI.Computability.BorderVNP.DiagonalSelectedLookupSites

/-! # Apply the signed host reader to an already selected frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term

/-- Use the existing sites and their evidence on every exterior and team, with
the wire, header equality and frame of this particular selection. -/
elab "originalHostAtSibling%" reader:term:max sibling:term:max : term => do
  let worker ← elabTerm reader none
  let s ← elabTerm sibling none
  let family := ``PreparationFrame.SelectedLookupSites
  let some ty ← whnfUntil (← inferType s) family
    | throwErrorAt sibling "expected the registered sibling sites"
  forallTelescope (← getConstInfo family).type fun parameters _ => do
    let mut arguments : NameMap Expr := {}
    for parameter in parameters, value in ty.getAppArgs do
      arguments := arguments.insert (← parameter.fvarId!.getUserName) value
    let field (name : Name) : MetaM Expr := do
      let some value := arguments.find? name | throwError "missing {name} on the selected sibling"
      return value
    let evidence ← field `evidence
    let method (name : Name) := mkAppN (Lean.mkConst name ty.getAppFn.constLevels!) (ty.getAppArgs.push s)
    let sites := method ``PreparationFrame.SelectedLookupSites.site
    let attained := method ``PreparationFrame.SelectedLookupSites.attained
    let per ← forallBoundedTelescope (← inferType sites) (some 2) fun coordinates _ => do
      let site := mkAppN sites coordinates
      let α ← inferType site
      let .sort level ← whnf (← inferType α) | throwError "missing the candidate site's universe"
      let existsSite := mkAppN (Lean.mkConst ``Exists.intro [level])
        #[α,mkAppN evidence coordinates,site,mkAppN attained coordinates]
      mkLambdaFVars coordinates existsSite
    return mkAppN worker #[evidence,per,← field `wire,← field `same,← field `F,s]

end TeamContraction

end BorderVNP
end Computability
end OAI
