import OAI.Computability.BorderVNP.DiagonalRestoredPublicationFields
import OAI.Computability.BorderVNP.DiagonalRestoredPinStates

/-! # The native publication at the pin state of its registered site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta PackedHistoryCircuit RoutingISA.Evaluator.SignedPrep

universe u v w

private theorem onReturnedState {M : Sort u} {B : Sort v} {R : Sort w}
    (P : M → B → R → Prop) {mac mac' : M} {bank bank' : B} {ram ram' : R}
    (hm : mac=mac') (hb : bank=bank') (hr : ram=ram') (publication : P mac bank ram) :
    P mac' bank' ram' := by
  cases hm; cases hb; cases hr
  exact publication

private def stateIndex (application : Expr) (name : Name) : MetaM Nat := do
  let mut signature := (← getConstInfo application.getAppFn.constName!).type
  for i in [:application.getAppNumArgs] do
    let .forallE n _ body _ := signature | throwError "missing the pin-state argument {name}"
    if n == name then return i
    signature := body
  throwError "the native pin has no argument named {name}"

/-- The original publication with its registered processor fields, macro
library, register bank and memory. All four equalities come from this
return's chosen fields and the boot node that actually ran the pin. -/
def restorePublicationOnReturn (receipt site : Expr) : MetaM Expr := do
  let published ← restorePublicationFields receipt site
  let same ← restoredPinEvidence site receipt
  let some pin ← whnfUntil (← inferType published) ``PublishedPin
    | throwError "expected the restored physical publication"
  let some candidate ← whnfUntil (← inferType site) ``CandidateSite
    | throwError "expected the site of the original return"
  let macroIndex ← stateIndex pin `mac
  let bankIndex ← stateIndex pin `postPin
  let ramIndex ← stateIndex pin `pinMem
  let oldMacro := pin.getAppArgs[macroIndex]!
  let oldBank := pin.getAppArgs[bankIndex]!
  let oldRam := pin.getAppArgs[ramIndex]!
  let newMacro := candidate.getAppArgs[← stateIndex candidate `mac]!
  let newBank := candidate.getAppArgs[← stateIndex candidate `reg]!
  let newRam := candidate.getAppArgs[← stateIndex candidate `mem]!
  let M ← inferType oldMacro
  let B ← inferType oldBank
  let R ← inferType oldRam
  let family ← withLocalDeclD `mac M fun mac =>
    withLocalDeclD `bank B fun bank =>
      withLocalDeclD `ram R fun ram => do
        let args := (pin.getAppArgs.set! macroIndex mac).set! bankIndex bank |>.set! ramIndex ram
        mkLambdaFVars #[mac,bank,ram] (mkAppN pin.getAppFn args)
  return mkAppN (mkConst ``onReturnedState [← getLevel M,← getLevel B,← getLevel R])
    #[M,B,R,family,oldMacro,newMacro,oldBank,newBank,oldRam,newRam,
      same.macros,same.registers,same.memory,published]

/-- The publication at its selected site's native fields, instruction library
and pin-return state. -/
elab (name := publicationOnRegisteredReturn) "restoredPublicationOnReturn%" receipt:term:max site:term:max : term => do
  restorePublicationOnReturn (← Elab.Term.elabTerm receipt none) (← Elab.Term.elabTerm site none)

end Diagonal

end BorderVNP
end Computability
end OAI
