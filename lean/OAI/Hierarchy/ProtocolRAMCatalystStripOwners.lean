import OAI.Hierarchy.ProtocolRAMCatalystStripStoredOwners
import OAI.Hierarchy.ProtocolRAMCalendarStripBuild

namespace OAI
/-! # Reserve-owner words computed by the mounted outer and purchased strip ROMs -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard BoughtSockets PurchaseFrozen
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
namespace Calendar.StripChart
open CatalogueRows StripDirectory
variable {z W k q depth w : ℕ}
local notation "N" => Stages z (2^W)
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R

variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
    (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

/-- A positive literal failure-live word places the outer ballot in the payload prefix. -/
theorem payload_entered (p a incoming : ℕ) (m : Memory w)
    (row : Fin (header F (withPorts s c b G) (.outer p a)).rows)
    (rowFit : row.val < 2^w) (prefixFit : 2^z < 2^w)
    (on : (build F (withPorts s c b G) (.outer p a) incoming).market.failures.live.eval m (row.val:Word w) ≠ 0) :
    row.val < 2^z := by
  change (Expr.branch .lt .row (.lit (2^z)) (.lit 1) (.lit 0)).eval m (row.val:Word w) ≠ 0 at on
  by_contra outside
  apply on
  simp only [Expr.eval,Comparison.test,Fin.lt_def,decide_eq_true_eq,
    Fin.val_cast_of_lt rowFit,Fin.val_cast_of_lt prefixFit,ite_eq_right outside]; rfl

/-- The inner ballot measures the affirmative flag at its original DFS row. -/
theorem purchased_entered (p a j t incoming : ℕ) (m : Memory w)
    (row : Fin (header F (withPorts s c b G) (.inner p a j t)).rows) :
    (build F (withPorts s c b G) (.inner p a j t) incoming).market.failures.live.eval m (row.val:Word w) =
      (flagBank (s.outer p a).market.shelf s.sampler z (2^W) k depth).read m (row.val:Word w) := rfl

end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
