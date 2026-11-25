import Lean

/-! # The geometry memory of the recorded native return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Lean Elab Term Meta

/-- Apply an installed-return theorem using the memory in the site's recorded
equality. This retains the original return and supplies its memory argument
without inferring the selected site's physical layout again. -/
elab (name := recordedReturnMemory) "recordedReturnMemory%" fn:term:max ret:term:max
    recorded:term:max : term => do
  let applyReturn ← elabTerm fn none
  let original ← elabTerm ret none
  let site ← elabTerm recorded none
  let memory ← mkProjection site `geometryMemory
  let some equality ← whnfUntil (← inferType memory) ``Eq |
    throwError "expected the recorded return's geometry memory equality"
  return mkAppN applyReturn #[original, equality.getAppArgs[1]!, memory]

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
