import OAI.Computability.BorderVNP.DiagonalOriginalReportedOwners

/-! # Reading a returned cell's owner on its sparse emission -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Meta Elab Term DiagonalTallyCellReports

/-- Read the original reported owners at the supplied sparse emission. The
prepared report determines its layout, ordered rows, cursor and description.
The allocation names the physical bank, and the emission carries both its
fit proof and its cell-count proof. -/
elab (name := originalOwnersAtEmission) "originalOwnersAtEmission% "
    actual:term:max registered:term:max team:term:max advance:term:max report:term:max
    seed:term:max allocation:term:max emission:term:max : term => do
  let owners ← elabTerm (← `(originalReportedOwners% $actual $registered)) none
  let u ← elabTerm team none
  let controls ← elabTerm advance none
  let reports ← elabTerm report none
  let prepared ← elabTerm seed none
  let allocated ← elabTerm allocation none
  let emitted ← elabTerm emission none
  let some input ← whnfUntil (← inferType prepared) ``PreparedReportInput |
    throwErrorAt seed "expected the input of the prepared report"
  let #[_, layout, _, _, rows, cursor, description] := input.getAppArgs |
    throwErrorAt seed "expected the source layout and ordered cells"
  let some bank ← whnfUntil (← inferType allocated) ``ReportAllocation |
    throwErrorAt allocation "expected the allocation of the report's receiving bank"
  let #[_, _, banks, _, _, _] := bank.getAppArgs |
    throwErrorAt allocation "expected the bank of the allocated report"
  let some source ← whnfUntil (← inferType emitted) ``FragmentRows.SparseEmission |
    throwErrorAt emission "expected the sparse emission on the returned cells"
  let data := source.getAppArgs
  let bankAt ← mkEqRefl (← mkProjection banks `bankStart)
  return mkAppN owners #[u, controls, reports, layout, rows, cursor, banks,
    description, prepared, allocated, bankAt, data[data.size-2]!, data.back!, emitted]

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
