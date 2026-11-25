import OAI.Computability.BorderVNP.DiagonalOriginalFundedInputTerm

/-! Elaborate original packet data that already has a type before passing it
to the ordinary funded input compiler. The compiled program and its implicit
indices still come from the original native operand implementation. -/

namespace OAI
namespace Computability
namespace BorderVNP

open Lean Meta Elab Term

namespace Diagonal.FundedNativeInputs

open private fromEvidence fill from OAI.Computability.BorderVNP.DiagonalOriginalFundedInputTerm

private def physicalInputs :=
  #[`repNet,`routingImage,`limit,`image,`rows,`scheduled,`observed₀,`writer,`keep]

/-- These expressions name existing data. Dependent introductions and holes
still need the original elaborator's expected type. -/
private partial def hasIndependentType (term : Syntax) : TermElabM Bool := do
  if term.isOfKind ``Lean.Parser.Term.paren then return ← hasIndependentType term[1]
  if term.isOfKind ``Lean.Parser.Term.proj then return ← hasIndependentType term[0]
  if term.isIdent then
    let name := term.getId
    let ctx ← getLCtx
    return (ctx.findFromUserName? name).isSome || (ctx.findFromUserName? name.getRoot).isSome
  if term.isOfKind ``Lean.Parser.Term.app then
    let fn := term[0]
    let name := fn.getId.eraseMacroScopes
    if fn.isIdent && #[`readings,`RoutingISA.readings,``RoutingISA.readings].contains name &&
        term[1].getArgs.size == 1 then
      return ← hasIndependentType term[1][0]
    return false
  return #["issuedNetworkField%","capturedReportWidth%","issuedOpenBits%","issuedOpenHeader%"].contains
    term[0].getAtomVal

/-- Store the written positional arguments under their original parameter names.
Only the explicit parameters consumed by the original call appear here. -/
private def namePositions (head : Expr) (given : NameMap Syntax) (positions : Array Syntax) :
    TermElabM (NameMap Syntax) := do
  forallTelescopeReducing (← inferType head) fun binders _ => do
    let mut named := given
    let mut index := 0
    let mut seen : NameSet := {}
    for b in binders do
      let decl ← b.fvarId!.getDecl
      let key := decl.userName
      if named.contains key && seen.contains key then throwError "ambiguous physical parameter {key}"
      seen := seen.insert key
      if decl.binderInfo.isExplicit && !named.contains key then
        let some term := positions[index]? | throwError "missing original positional operand {key}"
        named := named.insert key term
        index := index+1
    unless index == positions.size do throwError "unused positional operands for original source"
    return named

/-- Return the original nine data terms and every additional typed field which
can be obtained directly from the written expression. -/
private def recordedInputs (named : NameMap Syntax) : TermElabM (NameMap Expr) := do
  let mut typed := {}
  for key in physicalInputs do
    let some term := named.find? key | throwError "missing the original {key}"
    typed := typed.insert key (← elabTerm term none)
  for (key,term) in named.toList do
    if !typed.contains key && (← hasIndependentType term) then
      let state ← saveState
      try
        let value ← withoutErrToSorry <| elabTerm term none
        synthesizeSyntheticMVarsNoPostponing
        let value ← instantiateMVars value
        if value.hasMVar || value.hasSorry then state.restore
        else typed := typed.insert key value
      catch _ => state.restore
  return typed

/-- Assemble the original native reader using its recorded operand types.
Explicitly dependent terms are elaborated at the reader's expected types. -/
elab "originalFundedTypedInputs% " call:term:max : term => do
  let mut app := call.raw
  while app.isOfKind ``Lean.Parser.Term.paren do app := app[1]
  unless app.isOfKind ``Lean.Parser.Term.app do throwErrorAt call "expected an original funded reader application"
  let head ← elabTerm app[0] none
  let mut named : NameMap Syntax := {}
  let mut pos := #[]
  for term in app[1].getArgs do
    if term.isOfKind ``Lean.Parser.Term.namedArgument then
      let key := term[1].getId.eraseMacroScopes
      if named.contains key then throwErrorAt term "repeated funded reader input {key}"
      named := named.insert key term[3]
    else pos := pos.push term
  named ← namePositions head named pos
  let typed ← recordedInputs named
  let hidden ← fromEvidence typed
  fill head (← inferType head) named typed [] hidden

end Diagonal.FundedNativeInputs

end BorderVNP
end Computability
end OAI
