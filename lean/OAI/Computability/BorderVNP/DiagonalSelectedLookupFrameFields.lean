import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections
import OAI.Computability.BorderVNP.DiagonalSelectedLookupBuilders
import OAI.Computability.BorderVNP.DiagonalSelectedLookupHeader

/-! # The frame and wire extent of the selected lookup -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Lean Elab Term
open private reachedLookupProjection from OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections

/-- Read the installed frame with the same parameters and finite enumerations
as the selected lookup. -/
elab (name := originalLookupFrame) "originalLookupFrame% " source:term : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.installedFrame

/-- Read the stored equality of header extents from the original wire. -/
elab (name := originalLookupHeader) "originalLookupHeader% " source:term : term =>
  reachedLookupProjection source ``PreparationFrame.SelectedLookupSites.installedHeader

end TeamContraction

end BorderVNP
end Computability
end OAI
