import OAI.Computability.BorderVNP.DiagonalCalendarFundedReturnedFields
import Lean.Util.CollectFVars

/-! # Original sparse field values and their global ordinals -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace Diagonal
open Lean Meta RoutingISA RoutingISA.FragmentRows

private inductive Component where
  | family
  | readType (result : Name)
  | readProof

/-- Read the conclusion from the original marked sparse emission at its actual
cell and clock. Check that no report-allocation or funding operand escapes
into the indexed mathematical result. -/
private def fromAssigned (part : Component) : MetaM Expr := do
  let .defnInfo shape ← getConstInfo ``SignedCalendarAt.OriginalFundedFieldsType
    | throwError "expected the signed original funded fields"
  forallTelescope shape.value fun outer pl => do
    let some packed ← whnfUntil pl ``PLift | throwError "expected the actual pointwise report compiler"
    forallTelescopeReducing packed.getAppArgs[0]! fun inner target => do
      let some assigned ← whnfUntil target ``SparseEmission.AssignedFields
        | throwError "expected checked assigned sparse fields"
      let source := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.fundedReturnedFieldsAt) outer
      let fields := mkAppN (mkProj ``PLift 0 source) inner
      let inspect ← mkConstWithLevelParams ``SparseEmission.AssignedFields.withOrdinals
      let read := mkAppN inspect (assigned.getAppArgs.push fields)
      let result ← inferType read
      let fixed ← outer.filterM (fun x => return (← x.fvarId!.getDecl).userName != `funding)
      let keys := #[`f,`u,`fit,`cc,`emission]
      let called ← inner.filterM (fun x => return keys.contains (← x.fvarId!.getDecl).userName)
      let names ← called.mapM (fun x => return (← x.fvarId!.getDecl).userName)
      unless names == keys do throwError "expected the real field, team and physical emission; obtained {names}"
      let binders := fixed ++ called
      let family ← mkLambdaFVars binders result
      if family.hasFVar then
        let free := (Lean.collectFVars {} family).fvarIds
        let escaped ← free.mapM fun x => return (← x.getDecl).userName
        throwError "assigned result still mentions discarded operands {escaped}"
      match part with
      | .family => return family
      | .readType n => mkForallFVars (outer ++ inner) (mkAppN (← mkConstWithLevelParams n) binders)
      | .readProof => mkLambdaFVars (outer ++ inner) read

set_option maxHeartbeats 5400000
set_option maxRecDepth 13000
local elab "originalEmissionOrdinalIndex%" : term => do inferType (← fromAssigned .family)

/-- Indices of an original calendar emission, including its actual field,
team, emitter fit and physical cell alignment. -/
noncomputable abbrev SignedCalendarAt.OriginalEmissionOrdinalIndex : Type _ := originalEmissionOrdinalIndex%

/-- The returned original cell sizes, sparse bytes, scheduled ordinals,
report tails, widths and physical field values, indexed by the true emission. -/
noncomputable def SignedCalendarAt.originalEmissionOrdinalResult : SignedCalendarAt.OriginalEmissionOrdinalIndex := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← fromAssigned .family)
    Lean.Elab.Tactic.replaceMainGoal []

local elab "fundedEmissionReadbackType%" : term => do
  fromAssigned (.readType ``SignedCalendarAt.originalEmissionOrdinalResult)

/-- Every completed marked compiler provides the numerical and ordinal result
on precisely its own original field, team and native emission. -/
abbrev SignedCalendarAt.FundedEmissionReadback : Prop := fundedEmissionReadbackType%

/-- Reading an actual returned field exposes the original roster order and
the complete sparse values without another source or execution. -/
theorem SignedCalendarAt.fundedReturnedOrdinalReadout : SignedCalendarAt.FundedEmissionReadback := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← fromAssigned .readProof)
    Lean.Elab.Tactic.replaceMainGoal []

/-- Use the native fragment emitter's own orientation of the cell equality.
The public fit and cell proofs are implicit and fixed by the last argument. -/
private def allOriginalEmissions : MetaM Expr := do
  let family ← getConstInfo ``SignedCalendarAt.originalEmissionOrdinalResult
  lambdaTelescope family.value! fun xs _ => do
    unless xs.size ≥ 5 do throwError "missing physical emission operands"
    let original := xs.extract 0 (xs.size-5)
    let fields := xs[xs.size-5]!
    let team := xs[xs.size-4]!
    let oldFit := xs[xs.size-3]!
    let some schema ← whnfUntil (← inferType xs.back!) ``SparseEmission
      | throwError "expected the actual sparse emission"
    let operands := schema.getAppArgs
    let align ← inferType operands.back!
    withLocalDecl `fit .implicit (← inferType oldFit) fun fit => do
      withLocalDecl `cc .implicit align fun cc => do
        let shape := mkAppN schema.getAppFn ((operands.extract 0 (operands.size-2)) ++ #[fit,cc])
        withLocalDeclD `e shape fun e => do
          let aligned ← mkEqSymm cc
          let result := mkAppN (← mkConstWithLevelParams family.name)
            (original ++ #[fields,team,fit,aligned,e])
          let statement ← mkForallFVars #[fields,team,fit,cc,e] result
          let index ← mkLambdaFVars original statement
          if index.hasFVar then throwError "an original fit or cell proof escaped"
          return index

local elab "allOriginalEmissionIndex%" : term => do inferType (← allOriginalEmissions)

/-- The calendar operands fixing the entire original emission roster. -/
noncomputable abbrev SignedCalendarAt.OriginalEmissionRosterIndex : Type _ := allOriginalEmissionIndex%

/-- The numerical values and order of all original sparse emissions. Applying
a proof to the issued field, team and emission recovers its native result. -/
noncomputable def SignedCalendarAt.AllOriginalEmissionOrdinals : SignedCalendarAt.OriginalEmissionRosterIndex := by
  run_tac
    (← Lean.Elab.Tactic.getMainGoal).assign (← allOriginalEmissions)
    Lean.Elab.Tactic.replaceMainGoal []

end Diagonal

end BorderVNP
end Computability
end OAI
