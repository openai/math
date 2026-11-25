import OAI.Hierarchy.TaggedWideCalendarDatePins
import OAI.Hierarchy.TaggedWideSpillDates

namespace OAI
/-! # The fixed control-address offset of the actual second per-date spill page -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU.SpillDates
open SiteControls WireTelescope.PassMatrix
variable {T deg : ℕ} (z : SpillDates T) (start : ℕ)
local notation "G" => z.original

/-- The second date page uses the same control stride after all ordinary
signed control sheets. This shift applies uniformly to every date. -/
def spillControlWork := z.roleRoot start 2+T*stride (fun j=>((G).control j).span (G).sites)

theorem spillControlBase (j : Fin T) :
    (G).controlBase (z.spillControlWork start) j=z.spillStart start j := by
  unfold spillControlWork SpillDates.spillStart Dated.controlBase Dated.maskStart Dated.controlStart Dated.rolesEnd
    offset endOf
  omega

theorem spillControlAddress (j : Fin T) (s : Fin (G).sites) (f : SiteControls.Field deg) :
    controlAddress G (z.spillControlWork start) j s f=
      z.spillStart start j+1+s.val*((G).controlColumns j)+(fieldNumber deg f).val := by
  rw [controlAddress,z.spillControlBase]


end Hierarchy.ProtocolRAM.Calendar.WideCPU.SpillDates

end
end OAI
