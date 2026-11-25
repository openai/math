import OAI.Hierarchy.ProtocolRAMCatalystBirthOwner

namespace OAI
/-! Address bound for the owner scan of the current dated strip attempt. -/
noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open scoped Classical Fin.CommRing

namespace Calendar.StripChart
open CatalystArchive CatalogueRows StripDirectory BoughtSockets PurchaseFrozen
variable {z W k q depth w : ℕ}
local notation "N" => Stages z (2^W)
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

theorem ledger_attempt_fits (arena : Arena) (x : Attempt) (limit : ℕ) (word : limit < 2^w)
    (tab : G.column+ColumnROM.words z (2^W) k ≤ limit)
    (cover : ColumnROM.Cover z W G.directory.remapBase G.directory.sitesBase G.directory.superBase
      G.oldGroups G.bins G.height limit)
    (top : (header (z:=z) (d:=2^W) (k:=k) (q:=q) (depth:=depth) F
      (withPorts (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G) x).stop ≤ limit)
    (localBanks : BirthBankFits (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s G.directory.keysBase limit x) :
    ((ownerLedger s c b G F arena).term (.attempt x)).Fits w limit :=
  datedOwnerWords_fits s c b G F x 0 word tab cover top localBanks

end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
