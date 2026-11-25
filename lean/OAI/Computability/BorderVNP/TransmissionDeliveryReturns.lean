import OAI.Computability.BorderVNP.TransmissionDataReceipt
import OAI.Computability.BorderVNP.TransmissionSourceRegion

/-! # Reading the placed directory using the common public scheduler -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open Packing.Directory (Row)
open CellSparse.Packet.Source (Receipt)

variable {R r t d link inner n w : ℕ} {Edge : Type}
variable {G : Wiring R r t d link inner n Edge} {pin : Fin d → Bool}
variable {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}

/-- The actual team returns on one common native scheduling table. Scalar room for
the processor and substitution regions locates every source before the receiver
banks, independently of data values. -/
structure ReturnedDelivery (G : Wiring R r t d link inner n Edge) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (L : WireLayout (R+1) r link)
    (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1))
    (origin stride : ℕ) (H : Fin (R+1) → TeamHistory w) (pins : Fin (R+1) → Pins.Layout) where
  /-- Positive native word width. -/
  word : 0 < w
  /-- The common public table layout. -/
  table : TableLayout
  /-- Physical entry snapshots of the actual transfer program. -/
  bank : ∀ u, HistoryBank G pin ext L.width L.header u (H u) (table.readExtent (pins u))
  /-- Actual destination assignments and source words from the installed tables. -/
  placed : ∀ u, PlacedImage (H u) D pp lp (fun c => (owner c).val) origin stride (pins u) (table.readExtent (pins u))
  /-- The RAM snapshots at the true native relay comparisons. -/
  relay : ∀ v, TransferBank G pin ext L.width w L.header v
  /-- All relay comparisons hold, obtained by `TransferBank.checked_of_return`. -/
  checked : ∀ u v, ∀ p : Hop L.three L.width u v, RelayWordAgrees (readings (relay v).pub)
    (readings (relay v).mem) u v p.1 (p.2.val/(R+1-2))
  /-- Its four public columns, identical at every team. -/
  row : ℕ → TableRow
  /-- Actual before-scheduling RAM at each team. -/
  before : Fin (R+1) → ℕ → ℕ
  /-- The integer team dimension agrees with the chosen cluster. -/
  teams : R+1 = table.teams
  /-- The physical wire schedule uses the widths computed by the row loop. -/
  widths : L.width = tableWidth table row teams
  /-- The true scheduler arrays fit the RAM. -/
  allocated : table.Allocated w
  /-- Endpoint numbers and interval-width arithmetic fit their native words. -/
  rowsFit : table.RowsFit w row
  /-- The four public input columns are stored at their descriptor addresses. -/
  records : ∀ u, table.recordsMatch row (before u)
  /-- The actual scheduler memory image survives to transmission. -/
  image : ∀ u, table.Image row (before u) (readings (H u).initial)
  /-- Each history parses the real two-cursor table from this RAM. -/
  ranges : ∀ u, (H u).rows = tableRange table (H u).initial
  /-- Each native return scanned the complete common directory. -/
  fullCount : ∀ u, (H u).count = table.count
  /-- The placed data prefix lies within the scheduler's public row count. -/
  prefixCount : (D.directory pp lp).length ≤ table.count
  /-- Nonempty physical processor population. -/
  positive : 0 < D.processors
  /-- Actual processor count and literal width at the compiled data writer. -/
  dimensions : ∀ u, D.processors = (pins u).processors ∧ D.literal = (pins u).literal
  /-- The processor input region and substituted source array end before the receiver banks. -/
  sourceRoom : ∀ u, (pins u).processors*(pins u).stride ≤ origin ∧ (pins u).ibase+(pins u).count ≤ origin

variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}

/-- A true populated raw row, at any source lane, is delivered to the consumer's
absolute slot by the returned native programs. Common ordinals and demand bounds
follow from each real scheduler image. -/
theorem ReturnedDelivery.receipt (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins)
    (r : Row) (hr : r ∈ D.directory pp lp) (e : ℕ) (he : e < r.width)
    (u : Fin (R+1)) (sourceTeam : r.team = u.val) :
    Receipt (H u) (H (owner r.cell)) (r.sourceBase (pins u)+e) (origin+r.cell*stride+r.slot+e) := by
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hr
  let i : Fin (D.directory pp lp).length := ⟨k,hk⟩
  let j : Fin (D.directory pp lp)[i.val].width := ⟨e,he⟩
  apply receipt_of_placed f.word f.bank f.placed f.relay f.checked (f.table.ordinal f.row) _ _ i j u _ sourceTeam rfl
  · exact D.source_below pp lp (List.getElem_mem hk) f.positive he (pins u) (f.dimensions u).1 (f.dimensions u).2
      (f.table.readExtent (pins u)) (f.table.readExtent_bounds _).2.1 (f.table.readExtent_bounds _).2.2
  · intro v p
    rw [f.ranges]
    exact (tableRange_fields (f.image v) f.allocated (f.records v) (p.isLt.trans_le f.prefixCount)).2.2.2.2
  · intro v p
    generalize (f.bank v).initial.dst = dst
    rw [f.ranges,f.widths]
    exact ScheduledRange.of_table (f.image v) f.allocated f.rowsFit (f.records v) _ f.teams (p.isLt.trans_le f.prefixCount)

end TeamContraction

end BorderVNP
end Computability
end OAI
