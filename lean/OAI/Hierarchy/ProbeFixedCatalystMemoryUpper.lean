import OAI.Hierarchy.ProbeFixedCatalystCalendarUpper
import OAI.Hierarchy.ProtocolRAMCatalystTerminalUpper

namespace OAI
/-! # Retention above the full native calendar and its terminal settlement -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart CoreBoard
open CatalystArchive CoreRoute TerminalLayout
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (h width : ℕ)

theorem catalyst_upper {n count : ℕ} (L : OwnerLedger) (stock : Bank)
    (stride start reserveAmount attempts : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (recipes : Recipes) (g : Source) {I J : Type*} [Fintype I] [Fintype J]
    {core : I→List (Fin P.catalogue.rows)} {center : J→List (Fin P.catalogue.rows)}
    (enum : Fin (Fintype.card (Slots h (2^v.W) k))≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (m : PurchaseFrozen.Shelf.Mem h (2^v.W)) (slices : List PaidWidths.Slice)
    (x : ℕ) (ledger : L.arena=ownerArea
      (pageBits v.mesh (v.privateArena P h width) stock stride P.catalogue.rows (Fintype.card (Slots h (2^v.W) k)) count n) stride)
    (rows : ∀e∈events v.mesh,L.rows e ≤ stride) :
    let A:=v.privateArena P h width
    let r:=Fintype.card (Slots h (2^v.W) k)
    let bits:=pageBits v.mesh A stock stride P.catalogue.rows r count n
    let b:=settlement bits stock
    let owners:=sinkBank start n r P.catalogue.rows
    let sink:=P.catalogue.sink r b (TerminalLayout.source bits) (table bits) (TerminalLayout.destination bits) owners
    let C:=v.nativeChart P h width r b (TerminalLayout.source bits) (table bits) (TerminalLayout.destination bits) owners
    let checked:=checkedOut C (A.endAddress v.mesh) m
    let annual:=result (L.scans v.mesh count)
      (PaidWidths.output b.width P.catalogue.rows (TerminalLayout.source bits) slices checked)
    let archive:=result (CoreRoute.stages b recipes g v.sampler h v.W k attempts) annual
    extent bits slices≤x → Calendar.mounted C (events v.mesh) m →
      PaidWidths.Mounted b.width P.catalogue.rows (TerminalLayout.source bits) slices checked →
      sink.output (ReserveUse.output (reserve start n bits) b reserveAmount site debit archive) enum ci cj x=m x := by
  intro A r bits b owners sink C checked annual archive upper live paid
  have endLt : A.endAddress v.mesh<2^bits := by
    have hroom : footprint v.mesh A stock stride P.catalogue.rows r count n<2^bits:=Nat.lt_log2_self
    unfold footprint at hroom
    omega
  have top : 28*2^bits≤x:=(le_max_left ..).trans upper
  exact (settled_above v.mesh A P.catalogue L stock stride start reserveAmount site debit v.sampler attempts
    recipes g enum ci cj checked slices x ledger rows upper paid).trans
    (v.catalyst_calendar_upper P h width r b (TerminalLayout.source bits) (table bits) (TerminalLayout.destination bits)
      owners m x (endLt.trans_le ((Nat.le_mul_of_pos_left _ (by decide : 0 < 28)).trans top)) live)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
