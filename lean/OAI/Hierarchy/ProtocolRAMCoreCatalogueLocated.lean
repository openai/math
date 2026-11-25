import OAI.Hierarchy.ProtocolRAMCoreCatalogueSource
import OAI.Hierarchy.ProtocolRAMCataloguePruning

namespace OAI
/-! # Core endpoint decoding for geometric pruning -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups
open scoped Classical Fin.CommRing
variable {w h W k R H attempts : ℕ} {S : PurchaseSampler}

theorem Rows.located {c : CatalogueRows.CoreSource} {order : Fin R ≃ Edges S h (2^W) k}
    {dir : Directory (reserved h W (copies k attempts)) H} {π : Equiv.Perm (Fin (2^h))}
    {M : ℕ} {m : Memory w} (rows : Rows c order dir π M m) (depth : ℕ)
    (marked : Marks h W k attempts) (r : Fin R) (fits : siteLast h (2^W) k+1≤2^w)
    (metric : coreCode S M (order r)<2^w) :
    CatalogueRows.Located S π depth marked M (c.view m (r.val:Word w)) (.inl (order r)) := by
  obtain ⟨_,left,right,scale,_⟩ := rows r
  have read (x : Site h (2^W) k) :
      (((siteNumber h (2^W) k x).val:Word w)).val=(siteNumber h (2^W) k x).val :=
    Fin.val_cast_of_lt ((siteNumber h (2^W) k x).isLt.trans_le fits)
  exact ⟨(congrArg Fin.val left).trans (read _),(congrArg Fin.val right).trans (read _),
    (congrArg Fin.val scale).trans (Fin.val_cast_of_lt metric)⟩

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
