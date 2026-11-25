import OAI.Hierarchy.TaggedWideSpillDates
import OAI.Hierarchy.ProbeFixedWideDated
import OAI.Hierarchy.ProbeFixedWideSpillRank
import OAI.Hierarchy.ProbeFixedWideSpillMiddle

namespace OAI
/-! # The true dated spill and preclip inventories under one fixed native program -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width ell unitCost bits rankFirst : ℕ)
local notation "T" => (events v.mesh).length
local notation "g" => v.wideDated h width ell unitCost
local notation "page" => v.wideSpillPage h width bits rankFirst

def wideSpillDates : WideCPU.SpillDates T where
  original := g
  middle j := v.wideSpillMiddle h width bits j.val (page j.val)
  only paid j := WideCPU.spillOnly (v.wideRoleInventory h width bits (j.val+1)) (page j.val) paid
  attempt j := match (events v.mesh).get j with
    | .attempt _=>true
    | .feed _=>false
  cap := v.wideNeighborCap width unitCost

theorem wide_spill_columns (i : Fin T) :
    (g).controlColumns i=SiteControls.fieldCount (g).roleCount := rfl

def wideSpillDateEnd :=
  (v.wideSpillDates h width ell unitCost bits rankFirst).endAt (v.wideSpillRankEnd h width bits rankFirst)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
