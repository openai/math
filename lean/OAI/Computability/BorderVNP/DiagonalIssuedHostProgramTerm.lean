import OAI.Computability.BorderVNP.DiagonalPhysicalReturnCanonicalEntry

/-! # Applying the calibrated host reader to its original native returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term PackedHistoryCircuit

private def issuedProgramApplication (reader source epochSource publication memory packet : Syntax)
    (publicBank : Option Syntax) : TermElabM Expr := do
  let reader ← mkProjection (← elabTerm reader none) `down
  let pin ← elabTerm source none
  let some call ← whnfUntil (← inferType pin) ``PublishedPin | throwError "expected the returned native pin"
  let epoch ← elabTerm epochSource none
  let published ← elabTerm publication none
  let equality ← elabTerm memory none
  let stored ← elabTerm packet none
  let some middle ← whnfUntil (← inferType equality) ``Eq | throwError "expected the middle RAM equality"
  let info ← getConstInfo ``PublishedPin
  let mut fields : NameMap Expr ← forallTelescope info.type fun parameters _ => do
    let mut fields : NameMap Expr := {}
    for parameter in parameters, value in call.getAppArgs do
      fields := fields.insert (← parameter.fvarId!.getUserName) value
    return fields
  fields := fields.insert `middle middle.getAppArgs[2]! |>.insert `pin pin |>.insert `epoch epoch
    |>.insert `published published |>.insert `epochMemory equality |>.insert `stored stored
  if let some bank := publicBank then fields := fields.insert `pub (← elabTerm bank none)
  forallTelescopeReducing (← inferType reader) fun parameters _ => do
    let mut result := reader
    for parameter in parameters do
      let binder ← parameter.fvarId!.getUserName
      let field := match binder with
        | `used => `usedPin
        | `cost => `profCost
        | `regs => `preRegs
        | `seen => `prePlace
        | name => name
      let some value := fields.find? field | throwError "missing native host parameter {field}"
      result := mkApp result value
      if binder == `stored then return result
    throwError "expected the complete host reader"

/-- Apply the host reader on the clock, registers and memory actually retained by this publication. -/
elab "issuedHostProgram% " reader:term:max pin:term:max epoch:term:max published:term:max
    memory:term:max packet:term:max : term =>
  issuedProgramApplication reader pin epoch published memory packet none

/-- Read these same returns with the public bank of the registered processor. -/
elab "issuedHostProgramOn% " reader:term:max bank:term:max pin:term:max epoch:term:max
    published:term:max memory:term:max packet:term:max : term =>
  issuedProgramApplication reader pin epoch published memory packet (some bank)

end Diagonal

end BorderVNP
end Computability
end OAI
