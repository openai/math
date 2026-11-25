import OAI.Computability.BorderVNP.DiagonalSignedSelectedCandidates

/-! # The original preparation frame on all returned candidate sites -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term TeamContraction TeamContraction.ProcessorSlots
open RoutingISA.Evaluator

private def frameHead (type : Expr) (head : Name) : MetaM Expr := do
  let some op ← whnfUntil type head | throwError "expected the observed {head}"
  return op

private def frameHeadPairs (model actual : Expr) : Array (FVarId × Expr) :=
  (model.getAppArgs.zip actual.getAppArgs).filterMap fun (x,v) =>
    if x.isFVar then some (x.fvarId!,v) else none

private def frameLevels (lhs rhs : Expr) : List (Name × Level) :=
  (lhs.getAppFn.constLevels!.zip rhs.getAppFn.constLevels!).filterMap fun (a,b) =>
    match a with
    | .param n => some (n,b)
    | _ => none

/-- Form the actual selected preparation frame from the candidate sites
already returned for each source exterior and team. -/
syntax "plannerCandidateFrame% " term:max term:max term:max term:max term:max term:max
    term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max
    term:max term:max term:max term:max : term

elab_rules : term
  | `(plannerCandidateFrame% $wiring $layout $header $width $pin $guess $dst $ib $hb $sb $fit $per
       $room $copies $processors $literal $teams $literalRoom $headRoom $valid) => do
    let lctx ← getLCtx
    let instances ← getLocalInstances
    let arg (stx : Syntax) (type : Option Expr := none) : TermElabM Expr :=
      withLCtx lctx instances (Term.elabTerm stx type)
    let G ← arg wiring
    let limits ← arg fit
    let sites ← arg per
    let geo ← frameHead (← inferType G) ``Wiring
    let bound ← frameHead (← inferType limits) ``RouteTableInputs
    let theoremInfo ← getConstInfo ``signed_selected_candidates
    forallTelescope theoremInfo.type fun ps _ => do
      let mut fields := #[]
      let mut us := []
      let mut property := none
      for p in ps do
        let name ← p.fvarId!.getUserName
        if name == `G || name == `fit then
          let real := if name == `G then geo else bound
          let pattern ← frameHead (← inferType p) real.getAppFn.constName?.get!
          fields := fields ++ frameHeadPairs pattern real
          us := frameLevels pattern real ++ us
        if name == `perPin then
          -- Read the property and the four initial memory functions on the very
          -- same exterior and team as the supplied candidate.
          let (more,levels,pred) ← forallBoundedTelescope (← inferType p) (some 2) fun _ prop => do
            let ex ← frameHead prop ``Exists
            let formal ← frameHead ex.getAppArgs[0]! ``SignedPrep.CandidateSite
            forallBoundedTelescope (← inferType sites) (some 2) fun actual body => do
              let witness ← frameHead body ``Exists
              let physical ← frameHead witness.getAppArgs[0]! ``SignedPrep.CandidateSite
              let mut found := frameHeadPairs formal physical
              for (f,v) in formal.getAppArgs.zip physical.getAppArgs do
                let fvar := f.getAppFn
                if fvar.isFVar && f.getAppNumArgs == 2 then
                  found := found.push (fvar.fvarId!, ← mkLambdaFVars actual v)
              let keep ← mkLambdaFVars actual witness.getAppArgs[1]!
              return (found,frameLevels formal physical,keep)
          fields := fields ++ more
          us := levels ++ us
          property := some pred
      let levels ← theoremInfo.levelParams.mapM fun n => do
        let some (_,u) := us.find? (·.1 == n) | throwError "missing site universe {n}"
        return u
      let mut op := Lean.mkConst theoremInfo.name levels
      let mut type ← inferType op
      for p in ps do
        let name ← p.fvarId!.getUserName
        let value ← match name with
          | `G => pure G | `skeleton => arg layout | `header => arg header | `len => arg width
          | `pin => arg pin | `guess => arg guess | `dst => arg dst
          | `ib => arg ib | `hb => arg hb | `sb => arg sb
          | `fit => pure limits | `perPin => pure sites | `P₀ => pure property.get!
          | `subRoom => arg room | `copied => arg copies
          | `processors => arg processors (some type.bindingDomain!)
          | `literal => arg literal (some type.bindingDomain!)
          | `teams => arg teams (some type.bindingDomain!)
          | `literalRoom => arg literalRoom | `headRoom => arg headRoom | `valid => arg valid
          | _ => do
            let some (_,v) := fields.find? (·.1 == p.fvarId!) | throwError "missing physical frame input {name}"
            pure v
        op := mkApp op value
        type := type.bindingBody!.instantiate1 value
      return op

end Diagonal

end BorderVNP
end Computability
end OAI
