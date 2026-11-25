import OAI.Hierarchy.TaggedWideFundedSelectedReturn
import OAI.Hierarchy.WidthSelectedSpillInputs

namespace OAI
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
set_option maxRecDepth 16384
set_option maxHeartbeats 3800000
set_option Elab.async false
set_option cleanup.letToHave false
open Lean Meta

private def retainedSpillProof (fact : Lean.Expr) : MetaM Lean.Expr := do
  let some p ← whnfUntil (← inferType fact) ``Exists
    | throwError "expected the selected paid run's real existential receipt"
  return mkAppN (mkConst ``Classical.choose_spec p.getAppFn.constLevels!) (p.getAppArgs.push fact)

/-- Recover the typed register specification from the actual
funded result, at its original binders. The retained type erases the ignored witness
argument of SpillDataType, and the selected register itself is the original choice. -/
private def addSelectedSpillRegisters : MetaM Unit := do
  let info ← getConstInfo ``wide_selected_local_return
  let current ← mkConstWithLevelParams ``wide_selected_local_return
  let inputsDecl ← mkConstWithLevelParams ``wide_selected_spill_inputs
  let typeName := mkPrivateName (← getEnv) `OAI.Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.selectedSpillRegisterSpecification
  -- Name the dependent field specification once for the selected register and its clients.
  let (st,sv,rt,rv) ← forallTelescope info.type fun xs _ => do
    let paid := mkAppN current xs
    let issued : Lean.Expr := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 paid))
    let reported ← retainedSpillProof issued
    let before ← retainedSpillProof (.proj ``And 0 reported)
    let captured ← retainedSpillProof before
    let paths : Lean.Expr := .proj ``And 0 captured
    let readout : Lean.Expr := .proj ``And 1 (.proj ``And 1 captured)
    let exist := mkApp readout paths
    let some existence ← whnfUntil (← inferType exist) ``Nonempty
      | throwError "the issued spill has no typed register receipt"
    let some rt ← whnfUntil existence.appArg! ``NativeSpillRegisters.Evidence
      | throwError "expected the physical register evidence of the issued spill"
    let actualSpec := rt.getAppArgs.back!
    unless actualSpec.getAppNumArgs == 39 &&
        actualSpec.getAppFn.constName?.any (fun n => n.getString! == "nativeRegisterFieldTypes") do
      throwError "expected the original native register field specification and its stored input bank"
    -- Keep the input field shared with the selected preclip archive.
    let spec := mkAppN actualSpec.getAppFn (actualSpec.getAppArgs.set! 38 (mkAppN inputsDecl xs))
    let namedSpec := mkAppN (mkConst typeName (info.levelParams.map Level.param)) xs
    let namedType := mkApp (mkConst ``NativeSpillRegisters.Evidence) namedSpec
    let val := mkApp2 (mkConst ``Classical.choice existence.getAppFn.constLevels!) namedType exist
    let specType ← inferType spec
    return (← mkForallFVars xs specType, ← mkLambdaFVars xs spec,
      ← mkForallFVars xs namedType, ← mkLambdaFVars xs val)
  let install (name : Name) (typ val : Lean.Expr) : MetaM Unit := do
    let shared := ShareCommon.shareCommon' #[typ,val]
    let typ := shared[0]!
    let val := shared[1]!
    if typ.hasMVar || typ.hasFVar || typ.hasSorry || val.hasMVar || val.hasFVar || val.hasSorry then
      throwError "an unresolved binder or recovered term remains in the register selection"
    addDecl (.defnDecl {
      name := name
      levelParams := info.levelParams
      type := typ
      value := val
      hints := .regular 0
      safety := .safe
    })
    modifyEnv (addNoncomputable · name)
  let registerName := `OAI.Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.wide_selected_spill_registers
  install typeName st sv
  install registerName rt rv
  addDocStringCore registerName "The original typed operand record used to execute every revenue and spill turn."

open Lean Elab Command in
run_cmd liftTermElabM do addSelectedSpillRegisters
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_spill_registers"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
