import OAI.Hierarchy.ProtocolRAMBoughtMaxMetric
import OAI.Hierarchy.ProtocolRAMBoughtCataloguePricedFrame
import OAI.Hierarchy.ProtocolRAMCoreCatalogueLocated

namespace OAI
/-! # Actual core geography of the joint catalogue readback -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.Public
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets Calendar
open scoped Classical Fin.CommRing
variable {h W k R K H attempts : ℕ} {S : PurchaseSampler}

theorem coreCode_le (S : PurchaseSampler) {h d k : ℕ} (M : ℕ) (e : Edges S h d k) :
    coreCode S M e≤ maxMetric M := by
  unfold maxMetric
  rcases e with (radius|cross|fixed)|paid <;> simp only [CoreBoard.coreCode] <;> omega

theorem metric_eventually (W M : ℕ) :
    ∀ᶠ h : ℕ in Filter.atTop,maxMetric M<2^Native.wordBits h (2^W) Native.copies := by
  apply Filter.eventually_atTop.2
  refine ⟨maxMetric M,fun h above=>?_⟩
  have power := (Native.height_extent h (2^W)).trans (Native.extent_word h (2^W) Native.copies).le
  exact (above.trans_lt Nat.lt_two_pow_self).trans_le power

theorem Readback.located {order : Fin R≃Edges S h (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups h (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^h))} {m : Boot.Tape h (2^W)}
    (actual : Readback order M groups packed v depth π m) (marks : Marks h W k attempts)
    (word : endAddress S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth≤2^Native.wordBits h (2^W) Native.copies)
    (precision : maxMetric M<2^Native.wordBits h (2^W) Native.copies) (r : Fin R) :
    let c := CoreCatalogue.sourceAt h W k attempts R K packed.groups H (CoreCatalogue.pointBits h W)
    CatalogueRows.Located S π depth marks M (c.view m (r.val:Word _)) (.inl (order r)) := by
  have ⟨key,outer⟩ := borders S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth
  have cols := (ProtocolRAMPurchaseSampler.lt_span (siteLast h (2^W) k+1)).le
  have size : ProtocolRAMPurchaseSampler.span (siteLast h (2^W) k+1)≤ColumnROM.words h (2^W) k := Nat.le_add_right ..
  exact actual.rows.located depth marks r (by omega) ((coreCode_le S M (order r)).trans_lt precision)

end Hierarchy.ProtocolRAM.BoughtSockets.Public
end

end OAI
