import OAI.Hierarchy.ProtocolRAMCalendarStripPorts

namespace OAI
/-! # Catalyst traversal through the installed occurrence directory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard BoughtSockets
open StripDirectory CatalogueRows StockCommit
open scoped Classical

variable {z W k q depth : ℕ}
local notation "N" => Stages z (2^W)
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel))

/-- The mounted directory selects the debited role and its ball. The located
board still supplies both kinds of radius port and the original tree. -/
def forestAtHeader (H : PortHeader) (old : Traversals) (a : Attempt) : Traversals :=
  let mask := chooseField D 0 (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a) H.fieldTerm
  let mate := chooseField D 0 (fun i => (radiusMate s c b G a i).atRow H.ballTerm) H.fieldTerm
  b.guardWalk {old with catalystMate := some (mask, mate)}

variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

theorem forestAtHeader_original (old : Traversals) (a : Attempt) :
    forestAtHeader s c b G (header F (withPorts s c b G) a) old a = forest s c b G F old a := rfl

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
