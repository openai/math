import OAI.Computability.BorderVNP.DiagonalBootedProfilePublication
import OAI.Computability.BorderVNP.DiagonalSignedCandidateSite

/-! # The published packet on its registered processor fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta PackedHistoryCircuit RoutingISA.Evaluator.SignedPrep

universe u

private theorem onEqualFields {α : Sort u} (published : α → Prop) {source target : α}
    (same : HEq source target) (receipt : published source) : published target :=
  eq_of_heq same ▸ receipt

private def fieldsIndex (application : Expr) : MetaM Nat := do
  let mut signature := (← getConstInfo application.getAppFn.constName!).type
  for i in [:application.getAppNumArgs] do
    let .forallE key _ body _ := signature | throwError "the native return has too few arguments"
    if key == `fields then return i
    signature := body
  throwError "expected the processor fields of the native return"

private def chosenSpecification (proof : Expr) : MetaM Expr := do
  let some ex ← whnfUntil (← inferType proof) ``Exists | throwError "expected a witnessed native return"
  let args := ex.getAppArgs
  return mkApp3 (mkConst ``Exists.choose_spec ex.getAppFn.constLevels!) args[0]! args[1]! proof

/-- Transport the actual publication to the fields of the site chosen for it.
The physical `PublishedSiteAt` witness first chooses the processor fields and
then the return. The return records their equality with the fields of the
wiring. Every other argument, including the RAM and the clock, comes from the
original publication. -/
def restorePublicationFields (receipt site : Expr) : MetaM Expr := do
  let some pin ← whnfUntil (← inferType receipt) ``PublishedPin
    | throwError "expected a published pin"
  let some registered ← whnfUntil (← inferType site) ``CandidateSite
    | throwError "expected the site of the original return"
  let index ← fieldsIndex pin
  let source := pin.getAppArgs[index]!
  let target := registered.getAppArgs[← fieldsIndex registered]!
  let some chosen ← whnfUntil source ``Exists.choose
    | throwError "expected the processor fields chosen by the physical publication"
  let publication := mkAppN (mkConst ``Exists.choose_spec chosen.getAppFn.constLevels!) chosen.getAppArgs
  let measured ← chosenSpecification publication
  let same := mkProj ``And 0 measured
  let some equality ← whnfUntil (← inferType same) ``HEq
    | throwError "expected the field equality recorded on the physical return"
  let ends := equality.getAppArgs
  let domain ← inferType source
  unless ← isDefEq domain (← inferType target) do
    throwError "the registered and allocated pin layouts have different field types"
  unless (← isDefEq ends[1]! source) && (← isDefEq ends[3]! target) do
    throwError "the field equality is for a different registered site"
  let predicate ← withLocalDeclD `fields domain fun replacement =>
    mkLambdaFVars #[replacement] (mkAppN pin.getAppFn (pin.getAppArgs.set! index replacement))
  return mkAppN (mkConst ``onEqualFields [← getLevel domain])
    #[domain,predicate,source,target,same,receipt]

/-- The native publication, indexed by the processor fields carried by its
actual registered site. -/
elab (name := restoredPublicationAtSite) "restoredPublicationFields%" receipt:term:max site:term:max : term => do
  restorePublicationFields (← Elab.Term.elabTerm receipt none) (← Elab.Term.elabTerm site none)

end Diagonal

end BorderVNP
end Computability
end OAI
