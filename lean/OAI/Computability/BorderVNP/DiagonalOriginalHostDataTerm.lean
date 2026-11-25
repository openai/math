import OAI.Computability.BorderVNP.RoutingISASignedPrepRange

/-! # Applying the host reader to the returned slotted writer and its actual packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term

/-- The original writer fixes the slot type, its finite enumeration and the three address maps.
They are common to the teams whose returned writers will use them. -/
private def returnedSlotInventory (writers : Expr) : TermElabM (Array Expr) := do
  forallBoundedTelescope (← inferType writers) (some 1) fun teams writerType => do
    unless teams.size == 1 do throwError "expected one returned writer per team"
    let some writer ← whnfUntil writerType ``SlottedWriter | throwError "expected the returned SlottedWriter"
    let operands := writer.getAppArgs
    let inventory := operands.extract (operands.size - 5) operands.size
    unless inventory.size == 5 do throwError "incomplete slotted writer inventory"
    for operand in inventory do
      if operand.containsFVar teams[0]!.fvarId! then throwError "the slot inventory varies by team"
    return inventory

/-- The raw input records the common volume used when the pinned packet was opened. -/
private def returnedPacketVolume (rawInputs : Expr) : TermElabM Expr := do
  forallBoundedTelescope (← inferType rawInputs) (some 1) fun teams inputType => do
    unless teams.size == 1 do throwError "expected one raw input per team"
    let some input ← whnfUntil inputType ``PinnedRawInput | throwError "expected the returned PinnedRawInput"
    let volume := input.getAppArgs.back!
    if volume.containsFVar teams[0]!.fvarId! then throwError "the packet volume varies by team"
    return volume

/-- Supply the original host reader from the first slot after its capacity bound through the
shared read. The packet fixes the volume and decoded declaration. The actual writer receipt
fixes the register bank. The resulting reader takes the original pin inputs next. -/
elab (name := nativeHostDataTerm) "nativeHostData% " callee:ident
    &"from" "[" frames:term "," processors:term "," guess:term "," inputs:term "," team:term "," writes:term "]"
    &"buffer" "[" old:term "," fresh:term "," gates:term "," outputs:term "," width:term "," off:term "," ell:term ","
      ctl:term "," bits:term "," claims:term "," pad:term "," raw:term "]"
    &"opening" rawInput:term:max &"reports" reg:term:max issued:term:max &"reads" shared:term:max : term => do
  let read (source : Term) : TermElabM Expr := elabTerm source none
  let reader ← elabTerm (← `(@$callee)) none
  let writers ← read writes
  let inventory ← returnedSlotInventory writers
  let rawFields ← read rawInput
  let volume ← returnedPacketVolume rawFields
  let source := inventory ++ #[← read frames, ← read processors, ← read guess, ← read inputs, ← read team, writers]
  let packet := #[← read old, ← read fresh, ← read gates, ← read outputs, ← read width, ← read off, ← read ell,
    ← read ctl, volume, ← read bits, ← read claims, ← read pad, ← read raw, rawFields]
  let atDecode := mkAppN reader (source ++ packet)
  let .forallE name domain _ _ ← whnf (← inferType atDecode) | throwError "missing the decoded declaration"
  unless name.eraseMacroScopes == `decoded do throwError "expected the decoded declaration, got {name}"
  let some equality ← whnfUntil domain ``Eq | throwError "the decoded declaration must be an equality"
  let decoded ← mkEqRefl equality.getAppArgs[1]!
  let afterRead := mkAppN atDecode #[decoded, ← read reg, ← read issued, ← read shared]
  let .forallE next _ _ _ ← whnf (← inferType afterRead) | throwError "missing the native pin continuation"
  unless next.eraseMacroScopes == `input do throwError "expected the native pin input, got {next}"
  return afterRead

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
