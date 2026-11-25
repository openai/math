import OAI.Computability.BorderVNP.DiagonalPublishedPostAtGuess
import OAI.Computability.BorderVNP.DiagonalRegisteredWriterFacts

/-! # Applying the published-writer constructor to its recorded physical operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Lean Meta Elab Term PackedHistoryCircuit Evaluator TeamContraction

private def inputNames (operand : Expr) (head : Name) : MetaM (NameMap Expr) := do
  let some app ← whnfUntil operand head | throwError "expected {head}"
  let mut remain := (← getConstInfo head).type
  let mut found : NameMap Expr := {}
  for value in app.getAppArgs do
    let .forallE name _ body binder := remain | throwError "unexpected argument in {head}"
    found := found.insert (if binder.isInstImplicit then `installedInventory else name) value
    remain := body
  return found

private def operand (provided : NameMap Expr) (name : Name) : MetaM Expr := do
  let some value := provided.find? name | throwError "missing recorded input {name}"
  return value

/-- Build the physical writer from the arguments stored by this request, pin and writer trace. -/
elab (name := writerAtGuess) "writerAtGuess%" guessEq:term:max headerEq:term:max exteriorEq:term:max stateEq:term:max
    geometryEq:term:max resident:term:max same:term:max published:term:max epoch:term:max
    directory:term:max writer:term:max written:term:max source:term:max : term <= goal => do
  let pin ← elabTerm published none
  let history ← elabTerm writer none
  let held ← elabTerm resident none
  let exterior ← elabTerm exteriorEq none
  let p ← inputNames (← inferType pin) ``PublishedPin
  let h ← inputNames (← inferType history) ``WriterHistory
  let b ← inputNames (← inferType held) ``BootResidence
  let some eq ← whnfUntil (← inferType exterior) ``Eq | throwError "expected exterior equality"
  let mut values ← inputNames goal ``WriterPostRequest.PublishedWriter
  values := values.insert `x eq.getAppArgs[1]! |>.insert `returned (← operand b `after)
    |>.insert `published pin |>.insert `resident held |>.insert `writer history |>.insert `exteriorEq exterior
  for (toName, fromName) in [(`dimension,`D),(`ports,`p),(`Port,`P),(`portWidth,`bits),
      (`directoryLayout,`dir),(`headerBits,`hdr),(`g,`v),(`pinReg,`postPin),
      (`registers,`preRegs),(`geometry,`prePlace),(`pinCost,`usedPin),(`profileCost,`profCost)] do
    values := values.insert toName (← operand p fromName)
  for name in [`fields,`installedInventory,`N,`cell,`edgeID,`portID,`original,`live,`pinMem] do
    values := values.insert name (← operand p name)
  for (toName, fromName) in [(`before,`r),(`after,`t),(`finalMemory,`mt),(`events,`es)] do
    values := values.insert toName (← operand h fromName)
  let mut proofs : NameMap (TSyntax `term) := {}
  for (name, stx) in [(`guessEq,guessEq),(`headerEq,headerEq),(`stateEq,stateEq),
      (`geometryEq,geometryEq),(`same,same),(`epoch,epoch),(`directory,directory),(`written,written),(`source,source)] do
    proofs := proofs.insert name stx
  let op ← mkConstWithFreshMVarLevels ``WriterPostRequest.PublishedWriter.fromPublicationAtGuess
  let mut ty ← inferType op
  let mut args := #[]
  while let .forallE name domain body binder := ty do
    let key := if binder.isInstImplicit then `installedInventory else name
    let value ← match values.find? key, proofs.find? key with
      | some val, _ => pure val
      | none, some stx => elabTerm stx (some (domain.instantiateRev args))
      | none, none => throwError "missing physical writer argument {key}"
    args := args.push value
    ty := body
  return mkAppN op args

private def selectedApplication (source : Syntax) : TermElabM (Expr × Expr) := do
  let selected ← elabTerm source none
  let some applied ← whnfUntil (← inferType selected) ``PreparationFrame.SelectedLookupSites |
    throwError "expected installed lookup sites"
  return (selected, applied)

/-- Read the writer receipt using the complete inventory carried by the selected site. -/
elab (name := recordedWriters) "recordedWriters%" source:term:max : term => do
  let (selected, native) ← selectedApplication source
  return mkAppN (mkConst ``PreparationFrame.SelectedLookupSites.returnedSiteWriters native.getAppFn.constLevels!)
    (native.getAppArgs.push selected)

/-- Keep the installed lookup's geometry and physical evidence while varying its wire, alignment, and frame. -/
elab (name := frameSelectionLike) "frameSelectionLike%" source:term:max : term => do
  let (_, applied) ← selectedApplication source
  let head := applied.getAppFn
  let args := applied.getAppArgs
  let prefixSize := args.size - 4
  let fixed := mkAppN head (args.extract 0 prefixSize)
  forallBoundedTelescope (← inferType fixed) (some 3) fun dynamic rest => do
    let names ← dynamic.mapM fun e => e.fvarId!.getUserName
    unless names == #[`wire,`same,`F] do
      throwError "expected wire, alignment and frame, found {names.toList}"
    let .forallE name _ _ _ ← whnf rest | throwError "expected selected site evidence"
    unless name == `evidence do throwError "expected selected site evidence, found {name}"
    mkLambdaFVars dynamic (mkApp (mkAppN fixed dynamic) args.back!)

/-- Specialize a family on selected frames to the original wire, alignment, frame, and selected sites. -/
elab (name := atOriginalFrame) "atOriginalFrame%" family:term:max source:term:max : term => do
  let (chosen, applied) ← selectedApplication source
  let args := applied.getAppArgs
  let tail := args.extract (args.size - 4) (args.size - 1)
  return mkAppN (← elabTerm family none) (tail.push chosen)

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
