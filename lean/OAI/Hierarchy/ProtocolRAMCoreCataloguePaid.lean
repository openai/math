import OAI.Hierarchy.ProtocolRAMCoreCatalogueBoot
import OAI.Hierarchy.ProtocolRAMCalendarPaidReporter
import OAI.Hierarchy.ProtocolRAMCalendarMarketFrame

namespace OAI
/-! # The boot's core geometry is the final paid serializer's geometry -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {w h W k R H attempts q goods n count r edges : ℕ} {S : PurchaseSampler}

theorem paid_retains {limit : ℕ} {mid : Memory w} (C : Chart w q goods) (flag : ℕ) (f : Sink r edges) (src : ℕ) (slices : List PaidWidths.Slice)
    (arch : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (ready : mounted C (events C.mesh) mid)
    (calendar : ∀x< limit, ∀e∈events C.mesh,outside C x e)
    (sources : ∀s∈slices,s.Fits f.banks.width edges src w)
    (targets : limit≤ flag ∧ limit≤ f.banks.width.base ∧ limit≤ f.banks.reserved.base ∧
      limit≤ f.banks.used.base ∧ limit≤ arch.scratch) :
    ∀x< limit,paidSource C flag f src slices arch reserve site debit mid x=mid x := by
  obtain ⟨fFlag,fWidth,fReserve,fUsed,fScratch⟩ := targets
  intro x hx
  rw [paidSource,ReserveUse.frame _ _ _ _ _ _ x (.inl (hx.trans_le fReserve)) (.inl (hx.trans_le fUsed))
    (.inl (hx.trans_le fScratch)),PaidWidths.frame _ _ _ _ _ x sources (hx.trans_le fWidth),
    checkedOut,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (hx.trans_le fFlag))]
  exact run_outside C (events C.mesh) mid x ready (calendar x hx)

theorem Rows.paid_source {c : CatalogueRows.CoreSource} {order : Fin R≃Edges S h (2^W) k}
    {dir : Directory (reserved h W (copies k attempts)) H} {π : Equiv.Perm (Fin (2^h))}
    {M limit : ℕ} {mid : Memory w} (rows : Rows c order dir π M mid) (fit : Fits c w limit)
    (C : Chart w q goods) (flag : ℕ) (f : Sink r edges) (src : ℕ) (slices : List PaidWidths.Slice)
    (arch : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (ready : mounted C (events C.mesh) mid)
    (calendar : ∀x< limit, ∀e∈events C.mesh,outside C x e)
    (sources : ∀s∈slices,s.Fits f.banks.width edges src w)
    (targets : limit≤ flag ∧ limit≤ f.banks.width.base ∧ limit≤ f.banks.reserved.base ∧
      limit≤ f.banks.used.base ∧ limit≤ arch.scratch) :
    Rows c order dir π M (paidSource C flag f src slices arch reserve site debit mid) :=
  rows.frame fit (paid_retains C flag f src slices arch reserve site debit ready calendar sources targets)

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
