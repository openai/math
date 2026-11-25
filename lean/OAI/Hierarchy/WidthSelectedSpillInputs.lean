import OAI.Hierarchy.TaggedWideFundedSelectedReturn

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

/-- Name the input-memory bank carried by the selected run's actual spill-register specification. -/
private def addSelectedSpillInputs : MetaM Unit := do
  let info ← getConstInfo ``wide_selected_local_return
  let current ← mkConstWithLevelParams ``wide_selected_local_return
  let (it, iv) ← forallTelescope info.type fun xs _ => do
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
    let spec := rt.getAppArgs.back!
    unless spec.getAppNumArgs == 39 &&
        spec.getAppFn.constName?.any (fun n => n.getString! == "nativeRegisterFieldTypes") do
      throwError "expected the original native register field specification and its stored input bank"
    let inputs := spec.getAppArgs.back!
    let inputType ← inferType inputs
    return (← mkForallFVars xs inputType, ← mkLambdaFVars xs inputs)
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
  let inputName := `OAI.Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.wide_selected_spill_inputs
  install inputName it iv
  addDocStringCore inputName "The indexed physical input memories named by the selected original spill registers."

open Lean Elab Command in
run_cmd liftTermElabM do addSelectedSpillInputs
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_spill_inputs"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
