import OAI.Hierarchy.ProtocolRAMBootHigh
import OAI.Hierarchy.ProtocolRAMCatalystSlabLayout
import OAI.Hierarchy.ProtocolRAMCalendarChargePages
import OAI.Hierarchy.ProtocolRAMCalendarStripBootSize
import OAI.Hierarchy.ProtocolRAMCatalystStripSpace

namespace OAI
/-! # Allocating the signed terminal banks before constructing the actual event arenas -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe CatalystArchive
open CoreRoute StripDirectory CoreBoard PurchaseFrozen
open scoped Classical Fin.CommRing

namespace StripChart.Slab
open ColumnWires
variable {z W k q depth : ℕ}
local notation "d" => 2^W
local notation "N" => Stages z d

theorem rows_before_install (s : Boards z d k q depth) (c : Mesh) (cat : CatalogueRows.Board)
    (g : PortBanks ((c.inject+c.cool)*c.outerFuel)) (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (area : Arena) :
    declaredRows c (ownerLedger s c cat g F area)=publicRows c z d k s.sampler.degree depth := by
  funext t
  unfold declaredRows publicRows
  split
  · cases t <;> rfl
  · rfl

theorem entries_before_install (s : Boards z d k q depth) (c : Mesh) (cat : CatalogueRows.Board)
    (g : PortBanks ((c.inject+c.cool)*c.outerFuel)) (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (area : Arena) :
    rowOnlyCount c (declaredRows c (ownerLedger s c cat g F area))=publicEntries c z d k s.sampler.degree depth := by
  rw [rows_before_install s c cat g F area]
  rfl

theorem terminal_origin (prior : Slab) (c : Mesh) (s : Boards z d k q depth) (cat : CatalogueRows.Board)
    (g : PortBanks ((c.inject+c.cool)*c.outerFuel)) (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] :
    let actual:=withTerminal prior c z d k s.sampler.degree depth cat.rows
    let installed:=install actual s c
    let A:=arena actual s
    let n:=rowOnlyCount c (declaredRows c (ownerLedger installed c cat g F A))
    let owner:=sinkBank (staticStart prior.headerEnd (Fintype.card (Slots z d k))) n (Fintype.card (Slots z d k)) cat.rows
    owner.base+owner.size=A.first ∧ actual.thresholdExtra=prior.thresholdExtra := by
  intro actual installed A n owner
  have same : n=publicEntries c z d k s.sampler.degree depth := entries_before_install installed c cat g F A
  dsimp only [owner]
  rw [same]
  exact ⟨rfl,rfl⟩

/-- The actual last occupied terminal input word has a height-independent
linear coefficient, accounting separately for current and purchased rows. -/
theorem enlarged_header_bound (prior : Slab) (c : Mesh) (s : Boards z d k q depth) (cat : CatalogueRows.Board)
    (g : PortBanks ((c.inject+c.cool)*c.outerFuel)) (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (header rows : ℕ) (small : prior.headerEnd≤header*2^z) (paid : cat.rows≤rows*2^z) :
    (withTerminal prior c z d k s.sampler.degree depth cat.rows).headerEnd≤
      (header+8*stripRecordFactor c d k s.sampler.degree depth+20*CatalystArchive.slotFactor d k+16*rows+16)*2^z := by
  have records:=declared_records s c cat g F (⟨0,0⟩ : Arena)
  rw [entries_before_install s c cat g F (⟨0,0⟩ : Arena)] at records
  have slots:=CatalystArchive.slot_count z d k (Nat.two_pow_pos _)
  have extra : 16≤16*2^z:=by simpa using Nat.mul_le_mul_left 16 (Nat.two_pow_pos z)
  have paired:=staticStart_le prior.headerEnd (Fintype.card (Slots z d k))
  apply (static_footprint (staticStart prior.headerEnd (Fintype.card (Slots z d k))) (publicEntries c z d k s.sampler.degree depth)
    (Fintype.card (Slots z d k)) cat.rows).trans
  nlinarith only [small,records,slots,paid,extra,paired]

/-- Specialization to the original paid header with both selector-charge
pages, the empty reserve, and its complete padded score-read footprint. -/
theorem charged_terminal_start (s : Boards z d k q depth) (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (t : TreeCosts) {phases X Y steps : ℕ} (H : EconomicHeader phases X Y steps) (extra : ℕ) :
    (outerReserve F s t H).base+(outerReserve F s t H).size ≤ (chargedSlab F s t H extra).headerEnd :=
  Nat.le_add_right ..

end StripChart.Slab
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
