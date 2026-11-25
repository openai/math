import OAI.Computability.BorderVNP.DiagonalSelectedHistoryHostTables
import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections

/-! # Reading the host tables on the selected frame's own wire layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Meta Elab Term
open private reachedLookupProjection from OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections

/-- Use the selected frame's exact source and inventory parameters when reading its original host tables. -/
elab "originalLookupHostTables% " source:term:max : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.onHistoryHostTables

end TeamContraction

end BorderVNP
end Computability
end OAI
