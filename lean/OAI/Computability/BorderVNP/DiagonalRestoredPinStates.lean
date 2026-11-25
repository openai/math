import OAI.Computability.BorderVNP.DiagonalBootedProfilePublication
import OAI.Computability.BorderVNP.DiagonalFrozenReturnInputs
import OAI.Computability.BorderVNP.DiagonalSignedCandidateSiteSelection

/-! # The native state shared by a published pin and its returning site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta PackedHistoryCircuit RoutingISA RoutingISA.Evaluator SignedPrep
open TeamContraction.ProcessorSlots

/-- Equalities from the physical publication to the state on which its registered site starts. -/
structure RestoredPinEvidence where
  /-- The installed instruction libraries coincide. -/
  macros : Expr
  /-- The register bank is the register projection of the same pin return. -/
  registers : Expr
  /-- The memory is the memory projection of the same pin return. -/
  memory : Expr

private def pinParameters (proof : Expr) (record : Name) : MetaM (NameMap Expr) := do
  let some instanceType ← whnfUntil (← inferType proof) record |
    throwError "expected an original {record}"
  let mut signature := (← getConstInfo record).type
  let mut fields := {}
  for value in instanceType.getAppArgs do
    fields := fields.insert signature.bindingName! value
    signature := signature.bindingBody!
  return fields

private def parameter (fields : NameMap Expr) (name : Name) : MetaM Expr := do
  let some value := fields.find? name | throwError "missing original pin coordinate {name}"
  return value

private def projectedData (record accessor : Name) (index : Nat) (field : Expr) : MetaM Expr := do
  if field.isAppOf accessor then
    return field.getAppArgs.back!
  if let .proj parent position value := field then
    if parent == record && position == index then return value
  throwError "expected the native projection {accessor}"

/-- Read the pointed equivalence from the register bank of the pin return:
the trace and state are paired, and the state consists of registers and memory. -/
private def pointedPins (registers : Expr) : MetaM (Expr × Expr) := do
  let pair ← projectedData ``Prod ``Prod.fst 0 registers
  let path ← projectedData ``Prod ``Prod.snd 1 pair
  let app ← projectedData ``Subtype ``Subtype.val 0 path
  unless app.isAppOfArity ``DFunLike.coe 6 do
    throwError "expected the actual application of the native pin equivalence"
  return (app.getAppArgs[4]!, app.getAppArgs[5]!)

private def stateProjection (pins guess : Expr) (index : Nat) : Expr :=
  let path := mkApp (mkProj ``Equiv 0 pins) guess
  mkProj ``Prod index (mkProj ``Prod 1 (mkProj ``Subtype 0 path))

private def sameProjection (published registered : Expr) : MetaM Expr := do
  unless (← isDefEq published registered) do throwError "different native pin endpoints"
  mkExpectedTypeHint (← mkEqRefl published) (← mkEq published registered)

private def stateEquality (oldPins newPins samePins guess : Expr) (index : Nat)
    (physical registered : Expr) : MetaM Expr := do
  let read ← withLocalDeclD `pins (← inferType oldPins) fun e =>
    mkLambdaFVars #[e] (stateProjection e guess index)
  let original ← sameProjection physical (stateProjection oldPins guess index)
  let actual ← sameProjection (stateProjection newPins guess index) registered
  mkEqTrans original (← mkEqTrans (← mkCongrArg read samePins) actual)

/-- Recover the actual installed-library equality and both state coordinates at a
published native return. The two pin equivalences are compared before applying
them to the common guess, keeping the large dependent return type abstract. -/
def restoredPinEvidence (site published : Expr) : MetaM RestoredPinEvidence := do
  let atSite ← pinParameters site ``CandidateSite
  let atPin ← pinParameters published ``PublishedPin
  let siteRegisters ← parameter atSite `reg
  let pinRegisters ← parameter atPin `postPin
  let (oldPins, guess) ← pointedPins pinRegisters
  let (newPins, given) ← pointedPins siteRegisters
  unless (← isDefEq guess given) do throwError "the registered site has a different pin guess"
  let samePins ← sameProjection oldPins newPins
  let registers ← stateEquality oldPins newPins samePins guess 0 pinRegisters siteRegisters
  let memory ← stateEquality oldPins newPins samePins guess 1
    (← parameter atPin `pinMem) (← parameter atSite `mem)
  unless newPins.isAppOf ``BootedPinStart.pins do throwError "expected the booted site's own pin equivalence"
  let node := newPins.getAppArgs.back!
  let some boot ← whnfUntil (← inferType node) ``BootedPinStart |
    throwError "missing the boot of the returned site"
  let macros := mkAppN (← mkConstWithLevelParams ``BootedPinStart.installed_routines_at) (boot.getAppArgs.push node)
  let some eqn ← whnfUntil (← inferType macros) ``Eq | throwError "expected the installed library equality"
  unless (← isDefEq eqn.getAppArgs[1]! (← parameter atPin `mac)) &&
         (← isDefEq eqn.getAppArgs[2]! (← parameter atSite `mac)) do
    throwError "the native library does not match its registered boot"
  return ⟨macros, registers, memory⟩

end Diagonal

end BorderVNP
end Computability
end OAI
