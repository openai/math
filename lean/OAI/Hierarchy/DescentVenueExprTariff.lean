import OAI.Hierarchy.DescentVenueExprBill
import OAI.Hierarchy.DescentVenueExprSlabs
import OAI.Hierarchy.DescentOverlapTariff

namespace OAI
/-! # Cost of gathering live operand expressions and changing their packing width -/
namespace Hierarchy.DescentVenueSlabs.ExprInputs
open DescentSIMDLookup ProtocolRAM
open DescentStaticWordColumn (names names_seq)
noncomputable section

theorem price (s : Shape) (src : Fin s.pages → Expr) (base w T : ℕ)
    (cost : ∀j, (src j).work ≤ T) (old : 0 < s.sourceLanes) (next : 0 < s.targetLanes) :
    ticks s src base + 7*names (program s src base w) ≤ tariff s T := by
  have copy := DescentResetStemProjectExpr.gather_clock src s.hosts s.groups s.sourceLanes base T cost
  have hardware := DescentResetStemProjectExpr.gather_names src s.hosts s.groups s.sourceLanes base w T cost
  change ProtocolRAM.clock (passes s src base) ≤ _ at copy
  change names (ProtocolRAM.program w (passes s src base)) ≤ _ at hardware
  have handoff := Overlap.tariff (work s base) (s.pages*s.hosts) s.groups s.sourceLanes
    s.targetLanes s.bits w (gathered s base) old next
  rw [program,names_seq,ticks,tariff]
  omega

end
end Hierarchy.DescentVenueSlabs.ExprInputs

end OAI
