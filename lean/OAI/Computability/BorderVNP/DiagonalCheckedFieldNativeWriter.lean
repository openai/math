import OAI.Computability.BorderVNP.DiagonalCalendarNativeWriterOnOriginal

/-! # The original native writer on its checked calendar fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term

/-- Recover the native writer service from the particular calendar used to
validate the original route on every pin, history and subtotal. -/
def nativeWriterOnCheckedRoutes (checks : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType checks) (some 3) fun _ result => do
    let some checked ← whnfUntil result ``CheckedRouteInputs |
      throwError "expected the checked physical route at every original pin"
    let some route ← whnfUntil checked.getAppArgs.back! ``SignedCalendarAt.frozenRoutedAt |
      throwError "expected the original physical calendar"
    let received := route.getAppArgs
    let sig ← getConstInfo ``SignedCalendarAt.frozenRoutedAt
    forallTelescope sig.type fun binders _ => do
      let names ← binders.mapM fun x => x.fvarId!.getUserName
      let some pin := names.idxOf? `i | throwError "missing the declared pin vector"
      let tail := #[`i, `hist, `claim, `template, `entries]
      unless names.extract pin received.size == tail do
        throwError "expected the original pin, history, claim, template and entry count"
      let writer := Lean.mkConst ``SignedCalendarAt.frozenNativeWriterOnOriginal
      return mkApp (mkAppN writer (received.extract 0 pin)) checks

/-- The actual native owner and scan family on the recorded checked routes. -/
elab (name := nativeWritersForChecked) "nativeWritersForChecked% " checks:term:max : term => do
  nativeWriterOnCheckedRoutes (← elabTerm checks none)

/-- The field of the recorded native writer on these validated routes. -/
elab (name := nativeCheckedFieldType) "nativeCheckedFieldType% " checks:term:max : term => do
  let family ← nativeWriterOnCheckedRoutes (← elabTerm checks none)
  let .forallE _ field _ _ ← whnf (← inferType family) | throwError "missing the native field"
  return field

/-- Recover the original writer and its actual native scan at the supplied field. -/
elab (name := nativeWriterForCheckedField) "nativeWriterForCheckedField% " checks:term:max field:term:max : term => do
  let family ← nativeWriterOnCheckedRoutes (← elabTerm checks none)
  let original ← elabTerm field none
  return mkApp family original

end Diagonal

end BorderVNP
end Computability
end OAI
