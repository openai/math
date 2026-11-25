import OAI.Computability.BorderVNP.FragmentRowsSparseLaunch
import OAI.Computability.BorderVNP.CellSparseExteriorBudget
import OAI.Computability.BorderVNP.CubeRouteEmitterInputs
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostRetention

/-! # The implicit indices of the original funded reader -/

namespace OAI
namespace Computability
namespace BorderVNP

open Lean Meta Elab Term

namespace Diagonal.FundedNativeInputs

/-- The original declaration gives each operand a name, including parameters
which are implicit in the application at the paper's calendar. -/
private def operandFields (routine : Name) (termType : Expr) : MetaM (NameMap Expr × Option Expr) := do
  let some applied ← whnfUntil termType routine
    | throwError "expected a {routine} in the original funded source"
  forallTelescope (← inferType applied.getAppFn) fun binders _ => do
    let mut fields : NameMap Expr := {}
    let mut inst := none
    for binder in binders, a in applied.getAppArgs do
      let decl ← binder.fvarId!.getDecl
      if decl.binderInfo.isInstImplicit then inst := some a
      else fields := fields.insert decl.userName a
    return (fields,inst)

private def findField (fields : NameMap Expr) (key : Name) : MetaM Expr := do
  let some val := fields.find? key | throwError "missing original operand {key}"
  return val

private def copy (data field : NameMap Expr) (pairs : List (Name × Name)) : MetaM (NameMap Expr) := do
  let mut found := data
  for (dst, src) in pairs do found := found.insert dst (← findField field src)
  return found

private def beforeSum (arg : Expr) (offset : Nat) : MetaM Expr := do
  let args := arg.getAppArgs
  if arg.isAppOf ``HAdd.hAdd || arg.isAppOf ``Nat.add then
    unless ← isDefEq args.back! (mkNatLit offset) do throwError "unexpected schedule offset, expected +{offset}"
    return args[args.size-2]!
  let mut n := arg
  for _ in [:offset] do
    let some next ← whnfUntil n ``Nat.succ | throwError "missing schedule offset +{offset}"
    n := next.getAppArgs[0]!
  return n

private structure Inputs where
  values : NameMap Expr
  networkEnumeration : Expr
  writerEnumeration : Expr

/-- Read the hidden dimensions and recorded memories from these visible
physical arguments. The two distinct finite enumerations belong to the
network image and the writer for the actual returned slots. -/
private def fromEvidence (visible : NameMap Expr) : MetaM Inputs := do
  let typed (key : Name) := do inferType (← findField visible key)
  let (net,_) ← operandFields ``Packing.CellAddressPhysical.Represents (← typed `repNet)
  let (_,some enumNetwork) ← operandFields ``Packing.RoutingOutputs.Image (← typed `routingImage)
    | throwError "missing the enumeration of the original network image"
  let mut found ← copy {} net [(`actualPorts,`n),(`stencilAxes,`d),(`keys,`k),(`inputDigits,`w),(`σ,`σ)]
  let some less ← whnfUntil (← typed `limit) ``LT.lt | throwError "missing reader address inequality"
  let la := less.getAppArgs
  let (reader,_) ← operandFields ``RoutingISA.SignedTaskArena.Layout.endAddress la[la.size-2]!
  found ← copy found reader [(`readerIn,`u),(`readerGuess,`v),(`readerGates,`k)]
  let some eq ← whnfUntil (← typed `image) ``Eq | throwError "missing opened publication equality"
  let (publication,_) ← operandFields ``RoutingISA.CellControlRows.Layout.published eq.getAppArgs[2]!
  found := found.insert `source (← findField publication `mem)
  let rowBits ← forallBoundedTelescope (← typed `rows) (some 1) fun _ body => do
    let (row,_) ← operandFields ``RoutingISA.FragmentRows.SparseCell body
    findField row `data
  found := found.insert `data rowBits
  let (paid,_) ← operandFields ``RoutingISA.SparseExterior.PrivateCallsAt (← typed `scheduled)
  found ← copy found paid [(`cost,`R),(`exponent,`k)]
  found := found.insert `breadth (← beforeSum (← findField paid `B) 10)
  found := found.insert `steps (← beforeSum (← findField paid `j) 1)
  let (owner,_) ← operandFields ``TeamContraction.ObservedOwned (← typed `observed₀)
  found ← copy found owner [(`group₀,`group),(`family₀,`F),(`rowBits₀,`raw)]
  let (writer,some enumWriter) ← operandFields ``RoutingISA.Evaluator.SlottedWriter (← typed `writer)
    | throwError "missing the enumeration of the recorded slotted writer"
  found ← copy found writer [(`I,`I),(`atSite,`cell),(`sourceKey₀,`id),(`widths₀,`width),(`sourcePins,`pins)]
  let (keep,_) ← operandFields ``FiniteEvaluator.CubeAllocation.HostRetention (← typed `keep)
  found := found.insert `before (← findField keep `written)
  return ⟨found,enumNetwork,enumWriter⟩

private partial def fill (fn ty : Expr) (supplied : NameMap Syntax) (cached : NameMap Expr)
    (pos : List Syntax) (hidden : Inputs) (seenWriter : Bool := false)
    (data : Array Expr := #[]) : TermElabM Expr := do
  let .forallE key domain rest bi ← whnf ty | do
    unless pos.isEmpty && supplied.isEmpty do throwError "unused arguments at end of original funded reader"
    synthesizeSyntheticMVarsNoPostponing
    let native ← instantiateMVars (mkAppN fn data)
    if native.hasMVar then throwError "the original funded reader still has unresolved operands"
    return native
  let advance (value : Expr) (named : NameMap Syntax) (positions : List Syntax) :=
    fill fn (rest.instantiate1 value) named cached positions hidden (seenWriter || key == `I)
      (data.push value)
  if let some item := supplied.find? key then
    if let some known := cached.find? key then advance known (supplied.erase key) pos
    else advance (← elabTerm item domain) (supplied.erase key) pos
  else if bi.isInstImplicit then
    advance (if seenWriter then hidden.writerEnumeration else hidden.networkEnumeration) supplied pos
  else if !bi.isExplicit then
    advance (← findField hidden.values key) supplied pos
  else
    let item :: tail := pos | throwError "missing positional input {key} to the original funded reader"
    advance (← elabTerm item domain) supplied tail

/-- Elaborate the stated native funded reader, preserving every source operand.
Its two finite enumerations and other implicit indices are already present in
the typed public geometry, sparse scan, return observation and writer. -/
elab "originalFundedInputs%" call:term:max : term => do
  let mut app := call.raw
  while app.isOfKind ``Lean.Parser.Term.paren do app := app[1]
  unless app.isOfKind ``Lean.Parser.Term.app do throwErrorAt call "expected a funded reader application"
  let head ← elabTerm app[0] none
  let mut named : NameMap Syntax := {}
  let mut positions := #[]
  for item in app[1].getArgs do
    if item.isOfKind ``Lean.Parser.Term.namedArgument then
      let key := item[1].getId.eraseMacroScopes
      if named.contains key then throwErrorAt item "repeated funded reader input {key}"
      named := named.insert key item[3]
    else positions := positions.push item
  let mut visible : NameMap Expr := {}
  for key in [`repNet,`routingImage,`limit,`image,`rows,`scheduled,`observed₀,`writer,`keep] do
    let some item := named.find? key | throwErrorAt call "need the authentic {key} for this funded reader"
    let term ← elabTerm item none
    visible := visible.insert key term
  let hidden ← fromEvidence visible
  fill head (← inferType head) named visible positions.toList hidden

end Diagonal.FundedNativeInputs

end BorderVNP
end Computability
end OAI
