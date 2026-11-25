import OAI.Hierarchy.DescentStageVenueSources
import OAI.Hierarchy.DescentStageVenueDate

namespace OAI
/-! The original funded-count column used by the ordinary node checkpoint. -/
namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open ProtocolRAM

/-- Original paid raster at the operand pitch. Out-of-range blocks on an arbitrary
numeric chart use its first physical block. -/
def metadataPaid (d : Date) (sources : Sources) (x : ℕ) : Expr :=
  .lookup (sources.paid (if x<2^d.k then x else 0)) .row

end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI
