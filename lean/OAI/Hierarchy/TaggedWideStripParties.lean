import OAI.Hierarchy.TaggedWideSiteNumber
import OAI.Hierarchy.TaggedWideSiteScatter
import OAI.Hierarchy.ProbePayloadPlacement
import OAI.Hierarchy.ProbeStripOccupancy

namespace OAI
/-! # The actual eligible strip parties in the native census -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.SiteDirectory
open AdaptiveProbe ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {h d k depth W : ℕ} (π : Equiv.Perm (Fin (2^h)))

def payloadParties :
    (Fin (2^h) × ColumnSite (PayloadStrip.Columns (Stages h d)) k) ↪ Fin (siteLast h d k+1) :=
  (payloadSitesAll π k).trans (siteNumber h d k).toEmbedding

def stageOrd : StageColumns h d ↪ Columns h d := Function.Embedding.inl.trans Function.Embedding.inr

variable (S : PurchaseSampler) (mark : StageAt h d → Fin k×Bool → Finset (Fin (2^h)))
    (unique : ∀s c c' r,r∈mark s c → r∈mark s c' → c=c')

def boughtParties : (LiveChains S π depth mark × ColumnSite (ChainStrip.Columns depth) k) ↪ Fin (siteLast h d k+1) :=
  ((allTreeSites S π depth mark unique).trans (stageOrd.prodMap (Function.Embedding.refl _))).trans
    (siteNumber h d k).toEmbedding

/-- `CatalogueRows.payload_column` reads the measured column on the original
permutation path. The public inverse site directory adds the finite party's
actual layer (including signed altimeters) at that row. -/
theorem payload_site {base : ℕ} (m : Memory W) (p : Fin (2^h))
    (i : ColumnSite (PayloadStrip.Columns (Stages h d)) k) (col : Expr)
    (ready : HistoryRoles.RoleROM.Mounted base (table h d k) m) (fit : size h d k≤2^W)
    (measured : col.eval m (p.val:Word W)=((Fintype.equivFin _ (payloadPlace π p i.1)).val:Word W)) :
    (cell base h d i.2 col).eval m (p.val:Word W)=((payloadParties π (p,i)).val:Word W) :=
  read m ready i.2 col _ _ fit measured

/-- The bought strip instead uses its immutable birth path's relative
ordinal (`StripChart.bought_column_tiles`). True MIS makes the embedding
injective over all retained centers and both radii of every axis. -/
theorem bought_site {base : ℕ} (m : Memory W) (p : LiveChains S π depth mark)
    (i : ColumnSite (ChainStrip.Columns depth) k) (row : Word W) (col : Expr)
    (ready : HistoryRoles.RoleROM.Mounted base (table h d k) m) (fit : size h d k≤2^W)
    (measured : col.eval m row=((Fintype.equivFin (Columns h d)
      (stageOrd (allStripColumns S π depth mark unique (p,i.1)))).val:Word W)) :
    (cell base h d i.2 col).eval m row=((boughtParties π S mark unique (p,i)).val:Word W) :=
  read m ready i.2 col _ _ fit measured

end Hierarchy.ProbeStage.CoreBoard.SiteDirectory

end
end OAI
