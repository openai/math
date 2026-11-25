import OAI.Computability.BorderVNP.DiagonalFundedNativePlacementCast
import OAI.Computability.BorderVNP.DiagonalFundedReportWordPlacement
import OAI.Computability.BorderVNP.DiagonalFundedCableRows

/-! # The original funded return at the two observed cable placements -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Elab Term RoutingISA.Evaluator RoutingISA.SignedTaskArena

/-- Put the original slotted writer and its signed report at the funded reader's
private and live placements using the cable-count equation in the same observation. -/
def fundedRowsWithRecordedSlots (reader cables writer report : Expr) : MetaM Expr := do
  let next ← whnf (← inferType reader)
  unless next.isForall && next.bindingName! == `slotted do
    throwError "expected the original funded slotted writer"
  let actual ← fundedNativeWriterAt cables writer next.bindingDomain!
  unless actual.isAppOf ``SlottedWriter.atEqualPlacements do
    throwError "expected the returned writer's private and live placement equality"
  let placements := actual.appArg!
  let retained ← mkAppM ``ReportWords.withEqualPlacements #[report, placements]
  return mkApp2 reader actual retained

/-- Finish an original sparse read with its actual observed cable rows, supplied
widths, bank addresses and mixed memories. Both private placement and signed
publication use the original edge index of that same funded field. -/
elab "fundedOriginalReportAtPlacements% " reader:term:max " at " "[" observations:term,* "]"
    " using " writer:term:max retained:term:max room:term:max : term => withoutErrToSorry do
  let fields ← observations.getElems.mapM fun t => elabTerm t none
  unless fields.size == 6 do throwError "expected the six original physical observations"
  let first ← exprToSyntax fields[0]!
  let wires ← elabTerm (← `(originalFundedCableRows% $first)) none
  let source := mkAppN (← elabTerm reader none) (fields.set! 0 wires)
  let slotted ← elabTerm writer none
  let words ← elabTerm retained none
  let some issued ← whnfUntil (← inferType slotted) ``SlottedWriter |
    throwErrorAt writer "expected the attained slotted writer"
  let #[_, _, _, _, _, pins, _, placed, base, inventory, enumeration, host, id, width] := issued.getAppArgs |
    throwErrorAt writer "unexpected original writer coordinates"
  let some saved ← whnfUntil (← inferType words) ``ReportWords |
    throwErrorAt retained "expected the returned signed report"
  let #[_, _, _, written, _, _] := saved.getAppArgs |
    throwErrorAt retained "unexpected signed report coordinates"
  let bank := mkAppN source #[base, placed, written, inventory, enumeration, host, id, width, pins]
  return mkApp (← fundedRowsWithRecordedSlots bank fields[0]! slotted words) (← elabTerm room none)

end Diagonal

end BorderVNP
end Computability
end OAI
