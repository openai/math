import OAI.Computability.BorderVNP.DiagonalProjectedOwnedReplay

/-! # Reading the original writer on an observed returned history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term

private def replayParameters (proof : Expr) (head : Name) : TermElabM (NameMap Expr) := do
  let some application ← whnfUntil (← inferType proof) head |
    throwError "expected {head} on the opened history"
  let info ← getConstInfo head
  forallTelescope info.type fun parameters _ => do
    let mut fields : NameMap Expr := {}
    for parameter in parameters, value in application.getAppArgs do
      fields := fields.insert (← parameter.fvarId!.getUserName) value
    return fields

private def replayParameter (fields : NameMap Expr) (name : Name) : TermElabM Expr := do
  let some value := fields.find? name | throwError "missing reached owner parameter {name}"
  return value

/-- Apply the shared writer replay with the gate identifiers and row count from the actual
handoff, and the owner and routed assignment from its original observation. -/
elab "reachedSharedOwner% " selected:term:max exterior:term:max history:term:max delivery:term:max
    tableEq:term:max rowEq:term:max writer:term:max substitution:term:max handoff:term:max seen:term:max : term => do
  let projection ← elabTerm selected none
  let some frame ← whnfUntil (← inferType projection) ``PreparationFrame.WriterProjection |
    throwError "expected the original writer projection"
  let hand ← elabTerm handoff none
  let observation ← elabTerm seen none
  let issued ← replayParameters hand ``OwnedHandoff
  let observed ← replayParameters observation ``ObservedOwned
  let replay := Lean.mkConst ``PreparationFrame.WriterProjection.owned_replay frame.getAppFn.constLevels!
  let original := mkAppN replay (frame.getAppArgs.push projection)
  let inputs := #[← replayParameter observed `owners, ← replayParameter issued `template,
    ← replayParameter issued `id, ← replayParameter issued `count, ← elabTerm exterior none,
    ← elabTerm history none, ← elabTerm delivery none, ← elabTerm tableEq none, ← elabTerm rowEq none,
    ← elabTerm writer none, ← elabTerm substitution none, ← replayParameter observed `q,
    ← replayParameter issued `F, hand, observation]
  return mkAppN original inputs

end TeamContraction

end BorderVNP
end Computability
end OAI
