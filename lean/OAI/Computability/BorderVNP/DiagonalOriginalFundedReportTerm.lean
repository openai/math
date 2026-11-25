import OAI.Computability.BorderVNP.DiagonalCalendarFundedPrefixAt
import OAI.Computability.BorderVNP.DiagonalFundedEmittedReport
import OAI.Computability.BorderVNP.DiagonalCalendarFundedReportAddresses
import OAI.Computability.BorderVNP.DiagonalCalendarFundedOriginalDemandRows

/-! # Returning the original funded report

The issued packet contains the native launch, returned rows and placement witnesses.
Read those fields once to construct the emitted report. Reindex that same value first at
the report addresses and then at the incoming rows of the original selected network.
The resulting term is an application of the three report constructors. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.OriginalFundedReport

open Lean Meta Elab Term RoutingISA FragmentRows CellPacketGeometry

private def atHead (e : Expr) (n : Name) : MetaM Expr := do
  let some a ← whnfUntil e n | throwError "wanted native head {n} (found {e.getAppFn})"
  return a

private def projection (e : Expr) (i : Nat) : MetaM Expr := do
  let t ← whnf (← inferType e)
  let some n := t.getAppFn.constName? | throwError "missing native pair at field {i}"
  return mkProj n i e

private def byName (xs : Array Expr) (n : Name) : MetaM Expr := do
  let some v ← xs.findM? (fun x => return (← x.fvarId!.getUserName) == n) | throwError "missing {n}"
  return v

private def chooseSpec (existsProof : Expr) : MetaM Expr := do
  let t ← atHead (← inferType existsProof) ``Exists
  return mkAppN (mkConst ``Classical.choose_spec t.getAppFn.constLevels!) (t.getAppArgs.push existsProof)

private def matchActual (actual formal : Expr) (head : Name) (xs : Array Expr)
    (input : Array (Option Expr)) : MetaM (Array (Option Expr)) := do
  let x ← atHead (← inferType actual) head
  let y ← atHead (← inferType formal) head
  let mut known := input
  for (n,v) in y.getAppArgs.zip x.getAppArgs do
    if let some j := xs.idxOf? n then known := known.set! j (some v)
  return known

/-- Apply the actual data constructor to all its operands. The original
seed, cursor and rows are taken from the checked issued return itself. -/
private def fundedSite (packet planner starts team prefixRun emission rows seed banked count directory : Expr) :
    MetaM Expr := do
  let made ← getConstInfo ``EmittedReport.fromFundedSite
  let patch ← projection packet 0
  let pair ← projection packet 1
  let launch ← projection pair 0
  let typed ← projection pair 1
  let issued := mkProj ``Subtype 0 typed
  let cert := mkProj ``Subtype 1 typed
  let right (x : Expr) := mkProj ``And 1 x
  let left (x : Expr) := mkProj ``And 0 x
  -- The saved shape is existential in the original ranges, followed by the
  -- physical placement and its source-shape proof. Both come from this return.
  let oldShape := left (right (right cert))
  let witnesses ← chooseSpec (← chooseSpec oldShape)
  let placed := left witnesses
  let geometry := right (right witnesses)
  let sourceShape ← atHead (← inferType geometry) ``TypedBatch.SourceShape
  let shapeRow := sourceShape.getAppArgs[sourceShape.getAppNumArgs-2]!
  let actualD ← atHead (← inferType directory) ``SiteWords.Directory
  let tags ← atHead actualD.getAppArgs[0]! ``Fin
  let rows₀ ← mkAppM ``Nat.pred #[actualD.getAppArgs.back!]
  let lastFields := right (right (right cert))
  let owned := left lastFields
  let reads := right lastFields
  let ownType ← atHead (← inferType owned) ``CellDispatch.OwnerTable
  -- The receipt states the logical read for every original row. The domain,
  -- index and expected call are the three operands of the final report.
  let callRead ← forallBoundedTelescope (← inferType reads) (some 1) fun i body => do
    let equality ← atHead body ``Eq
    let index := equality.getAppArgs[1]!.appArg!
    return (← inferType i[0]!, ← mkLambdaFVars i index, ← mkLambdaFVars i equality.getAppArgs.back!)
  forallTelescope made.type fun xs _ => do
    let empty : Array (Option Expr) := Array.replicate xs.size none
    let issuedData ← matchActual issued (← byName xs `issued) ``SparseEmission.IssuedReportData xs empty
    let found ← matchActual launch (← byName xs `launch) ``SparseEmission.NativeInputAt xs issuedData
    let named := [
      (`a, planner), (`U, starts), (`u, team), (`p, prefixRun), (`patch, patch),
      (`launch, launch), (`issued, issued), (`seed, seed), (`row, rows), (`emission, emission),
      (`same, left cert), (`banked, banked), (`emitted, left (right cert)), (`parameterCount, count),
      (`tags, tags.getAppArgs.back!), (`rows₀, rows₀), (`originalDirectory, directory),
      (`owner, ownType.getAppArgs.back!), (`owned, owned), (`Index, callRead.1),
      (`index, callRead.2.1), (`want, callRead.2.2), (`atCell, reads)]
    let indexLevel ← getDecLevel callRead.1
    let mut f := Lean.mkConst made.name [indexLevel]
    for x in xs, item in found do
      let n ← x.fvarId!.getUserName
      let value ← if n == `shape then do
        let expected ← whnf (← inferType f)
        let existential ← atHead expected.bindingDomain! ``Exists
        let combined ← mkAppM ``And.intro #[geometry,placed]
        let witness := Lean.mkConst ``Exists.intro existential.getAppFn.constLevels!
        pure (mkAppN witness (existential.getAppArgs ++ #[shapeRow, combined]))
      else if n == `copyCount then do
        let expected ← whnf (← inferType f)
        let equality ← atHead expected.bindingDomain! ``Eq
        mkEqRefl equality.getAppArgs[1]!
      else if let some (_,supplied) := named.find? (fun p => p.1 == n) then pure supplied
      else if let some value := item then pure value
      else throwError "the checked native issued packet does not supply {n}"
      f := mkApp f value
    return f

private def argumentName (formal : Expr) : MetaM Name := do
  let key ← formal.fvarId!.getUserName
  let type ← inferType formal
  if type.isAppOf ``Fintype && type.appArg!.isFVar then
    return (← type.appArg!.fvarId!.getUserName).appendAfter "_enum"
  return key

private def valuesOf (term : Expr) : MetaM (NameMap Expr) := do
  let some name := term.getAppFn.constName? | throwError "expected an application of a native report constructor"
  let info ← getConstInfo name
  forallBoundedTelescope info.type (some term.getAppNumArgs) fun xs _ => do
    let mut out : NameMap Expr := {}
    for x in xs, value in term.getAppArgs do out := out.insert (← argumentName x) value
    return out

private def requireValue (xs : NameMap Expr) (n : Name) : MetaM Expr := do
  let some value := xs.find? n | throwError "native declaration did not capture {n}"
  return value

private def supplyReport (op core input : Expr) : MetaM Expr := do
  -- Prefer the new report coordinates after the first reindexing. The original
  -- seed, native participant and destination still come from the issued packet.
  let raw ← valuesOf core
  let result ← atHead (← inferType input) ``Subtype
  let report ← atHead result.getAppArgs[0]! ``EmittedReport
  let view ← valuesOf report
  let same ← atHead (← inferType (← requireValue raw `same)) ``Eq
  let destFn ← atHead (← requireValue raw `recv) ``Packing.RoutingOutputs.NativeDemands.receiver
  let seed ← requireValue raw `seed
  let mut actual : NameMap Expr := raw
  for (n,v) in view.toList do actual := actual.insert n v
  actual := actual.insert `reportDirectory (← requireValue view `dir)
  actual := actual.insert `decl (← requireValue raw `declaration)
  actual := actual.insert `rows (← requireValue raw `rows₀)
  actual := actual.insert `directory (← requireValue raw `originalDirectory)
  actual := actual.insert `start (← requireValue view `live)
  actual := actual.insert `Seed (← inferType seed)
  actual := actual.insert `native same.getAppArgs.back!
  actual := actual.insert `destination (← requireValue (← valuesOf destFn) `bounds)
  forallTelescopeReducing (← inferType op) fun xs _ => do
    let vals ← xs.pop.mapM fun x => do requireValue actual (← argumentName x)
    return mkAppN op (vals.push input)

/-- Both transports have the same calibration prefix as the original source.
The address operation ends before the seed table. The demand operation also takes
that table and the history of the original field tuple. -/
private def originalOperations (origin history : Expr) (level : Level) : MetaM (Expr × Expr) := do
  let source ← atHead origin ``SignedCalendarAt.frozenFundedPrefixAt
  let declaration ← getConstInfo ``SignedCalendarAt.frozenFundedPrefixAt
  let parameters := source.getAppArgs
  let tableIndex ← forallBoundedTelescope declaration.type (some parameters.size) fun xs _ => do
    let some table ← xs.findIdxM? (fun x => return (← x.fvarId!.getUserName) == `values)
      | throwError "the original funded source is missing its seed table"
    return table
  let address := Lean.mkConst ``SignedCalendarAt.atFundedReportAddresses [level]
  let demand := Lean.mkConst ``SignedCalendarAt.fundedReportOnOriginalRows [level]
  return (mkAppN address (parameters.extract 0 tableIndex),
    mkAppN demand ((parameters.extract 0 (tableIndex+1)).push history))

/-- Construct the emitted report of the given source and history and apply its
two original reindexings. All returned data come from the same issued packet. -/
elab "originalFundedReport%" origin:term:max history:term:max planner:term:max
    starts:term:max team:term:max prefixRun:term:max emission:term:max packet:term:max
    rows:term:max seed:term:max banked:term:max count:term:max directory:term:max : term => do
  let term := fun (stx : TSyntax `term) => elabTerm stx none
  let core ← fundedSite (← term packet) (← term planner) (← term starts) (← term team)
    (← term prefixRun) (← term emission) (← term rows) (← term seed)
    (← term banked) (← term count) (← term directory)
  let level ← getDecLevel (← requireValue (← valuesOf core) `Index)
  let (addressOp, demandOp) ← originalOperations (← term origin) (← term history) level
  let addressed ← supplyReport addressOp core core
  supplyReport demandOp core addressed

end Diagonal.OriginalFundedReport

end BorderVNP
end Computability
end OAI
