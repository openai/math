import OAI.Hierarchy.ProtocolRAMCatalystArchivePrefix
import OAI.Hierarchy.ProtocolRAMCoreRouteDirectory
import OAI.Hierarchy.ProtocolRAMCatalystOwnerLedger
import OAI.Hierarchy.ProtocolRAMPaidWidthPrefixFrame

namespace OAI
/-! # Reading earlier archive words after the reserve and route settlement -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Calendar
open scoped Classical Fin.CommRing

namespace CatalystArchive.TerminalLayout
open ProbeStage ProbeStage.CoreBoard Calendar.CoreRoute

variable {w n count z W k : ℕ}

/-- Below the first width page, the complete terminal program reads back the
original checked output, including the flag and the entire paid history arena. -/
theorem settled_below_at {entries : ℕ} (c : Mesh) (A : Arena) (cat : CatalogueRows.Board) (L : OwnerLedger)
    (stock : Bank) (stride start n reserveAmount : ℕ) (site : Fin entries→Fin count) (debit : Fin entries→ℕ)
    (S : PurchaseSampler) (attempts : ℕ) (p : Recipes) (g : Calendar.CoreRoute.Source)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin cat.rows)} {center : J→List (Fin cat.rows)}
    (enum : Fin (Fintype.card (Slots z (2^W) k))≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (m : Memory w) (slices : List PaidWidths.Slice) (x : ℕ)
    (ledger : L.arena=ownerArea (pageBits c A stock stride cat.rows (Fintype.card (Slots z (2^W) k)) count n) stride) :
    let r:=Fintype.card (Slots z (2^W) k)
    let bits:=pageBits c A stock stride cat.rows r count n
    let b:=settlement bits stock
    let a:=reserve start n bits
    let sink:=cat.sink r b (source bits) (table bits) (destination bits) (sinkBank start n r cat.rows)
    let owner:=result (L.scans c count) (PaidWidths.output b.width cat.rows (source bits) slices m)
    let archive:=result (Calendar.CoreRoute.stages b p g S z W k attempts) owner
    x<2^bits → PaidWidths.Mounted b.width cat.rows (source bits) slices m →
      sink.output (ReserveUse.output a b reserveAmount site debit archive) enum ci cj x=m x := by
  intro r bits b a sink owner archive low mounted
  let B:=2^bits
  have lower : x<B:=low
  rw [archive_prefix_at bits start n reserveAmount cat stock site debit enum ci cj archive x
    (by change x<6*B;omega) (.inl low)]
  have route : archive x=owner x := by
    apply ProtocolRAM.result_below
    intro pass h
    simp only [Calendar.CoreRoute.stages,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · change x<4*B
      omega
    · change x<5*B
      omega
  rw [route]
  have keep : owner x=PaidWidths.output b.width cat.rows (source bits) slices m x := by
    apply ProtocolRAM.result_below
    intro step h
    obtain ⟨e,_,rfl⟩:=List.mem_map.mp h
    change x<L.arena.base c e
    rw [ledger]
    change x<2*B+position c e*stride
    omega
  rw [keep]
  exact PaidWidths.frame b.width cat.rows (source bits) slices m x (fun y hy=>(mounted y hy).1)
    (by change x<1*B;omega)

theorem settled_below (c : Mesh) (A : Arena) (cat : CatalogueRows.Board) (L : OwnerLedger)
    (stock : Bank) (stride start reserveAmount : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (S : PurchaseSampler) (attempts : ℕ) (p : Recipes) (g : Calendar.CoreRoute.Source)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin cat.rows)} {center : J→List (Fin cat.rows)}
    (enum : Fin (Fintype.card (Slots z (2^W) k))≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (m : Memory w) (slices : List PaidWidths.Slice) (x : ℕ)
    (ledger : L.arena=ownerArea (pageBits c A stock stride cat.rows (Fintype.card (Slots z (2^W) k)) count n) stride) :
    let r:=Fintype.card (Slots z (2^W) k)
    let bits:=pageBits c A stock stride cat.rows r count n
    let b:=settlement bits stock
    let a:=reserve start n bits
    let sink:=cat.sink r b (source bits) (table bits) (destination bits) (sinkBank start n r cat.rows)
    let owner:=result (L.scans c count) (PaidWidths.output b.width cat.rows (source bits) slices m)
    let archive:=result (Calendar.CoreRoute.stages b p g S z W k attempts) owner
    x<2^bits → PaidWidths.Mounted b.width cat.rows (source bits) slices m →
      sink.output (ReserveUse.output a b reserveAmount site debit archive) enum ci cj x=m x :=
  settled_below_at c A cat L stock stride start n reserveAmount site debit S attempts p g enum ci cj m slices x ledger

/-- The tape and row directories for the original paid slices can be read again
from a terminal memory with the checked history below the calendar end address. -/
theorem mounted_checked_prefix (c : Mesh) (A : Arena) (stock : Bank) (stride edges r count n : ℕ)
    (bank : Bank) (src : ℕ) (slices : List PaidWidths.Slice) (checked settled : Memory w)
    (arch : ∀s∈slices,PrefixWidths.Archived w (A.endAddress c) s)
    (mounted : PaidWidths.Mounted bank edges src slices checked)
    (same : ∀ x<2^(pageBits c A stock stride edges r count n),settled x=checked x) :
    PaidWidths.Mounted bank edges src slices settled := by
  have high : footprint c A stock stride edges r count n<2^(pageBits c A stock stride edges r count n) :=
    Nat.lt_log2_self
  unfold footprint at high
  exact PrefixWidths.mounted_of_archive bank edges src (A.endAddress c) slices checked settled arch mounted
    (fun x hx=>same x (by omega))

end CatalystArchive.TerminalLayout
end Hierarchy.ProtocolRAM
end

end OAI
