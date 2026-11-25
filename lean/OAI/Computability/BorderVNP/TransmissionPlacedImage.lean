import OAI.Computability.BorderVNP.TransmissionPlacedProtection
import OAI.Computability.BorderVNP.TransmissionHistoryReadback

/-! # Actual destination and source columns at one team's return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- Exclusive upper bound on the initialized processor tapes, substituted input
words and the live scheduling arrays needed during every data transfer. -/
def TableLayout.readExtent (tab : TableLayout) (pins : Pins.Layout) : ℕ :=
  max (tab.ordinals+tab.count) (max (pins.processors*pins.stride) (pins.ibase+pins.count))

/-- The three read regions fit below their common exclusive end. -/
theorem TableLayout.readExtent_bounds (tab : TableLayout) (p : Pins.Layout) :
    tab.ordinals+tab.count ≤ tab.readExtent p ∧ p.processors*p.stride ≤ tab.readExtent p ∧
    p.ibase+p.count ≤ tab.readExtent p := by unfold readExtent; omega

end RoutingISA

namespace RoutingISA.Transmission

open VPVNP.BurstRAM Packing.Directory Function

variable {w : ℕ}

/-- Source team and physical source origin in each scheduled seven-column record. -/
structure SourceColumns (rows : ℕ → Range w) (d : Layout) (pp lp : ℕ → ℕ × ℕ) (pins : Pins.Layout) : Prop where
  /-- The source team is read from the packed demand. -/
  team : ∀ i : Fin (d.directory pp lp).length, (rows i).teamA.val = (d.directory pp lp)[i.val].team
  /-- Literal or substituted data at the actual processor-relative address. -/
  source : ∀ i : Fin (d.directory pp lp).length, (rows i).source.val = (d.directory pp lp)[i.val].sourceBase pins

/-- Source columns from the scheduled image of the true seven-word data compiler. -/
theorem SourceColumns.of_writers {l : TableLayout} {row : ℕ → TableRow} {before : ℕ → ℕ} {after : Memory w}
    (image : l.Image row before (readings after)) (al : l.Allocated w)
    (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (emit : DataWriter.Layout) (pub : Arg → Word w) (m : Memory w) (g : Cube.SharedRows.Layout)
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) before)
    (frame : g.frame = (pub 0).val) (output : g.records = emit.output)
    (sched : l.records = emit.output) (count : g.dataCount = emit.count)
    (data : (d.directory pp lp).length = emit.count) (full : emit.count ≤ l.count)
    (sep : (pub 0).val+13 < emit.output ∨ emit.output+emit.count*7 ≤ (pub 0).val+13)
    (raw : ∀ i : Fin (d.directory pp lp).length,
      DataWriter.demandAt (readings m) (emit.input+i.val*7) = (d.directory pp lp)[i.val])
    (fitted : ∀ i : Fin (d.directory pp lp).length,
      ∀ x ∈ DataWriter.record emit (readings m) (d.directory pp lp)[i.val], x < 2^w) :
    SourceColumns (tableRange l after) d pp lp emit.pins := by
  have fields (i : Fin (d.directory pp lp).length) := DataWriter.range_fields image al
    (i.isLt.trans_le (data.trans_le full)) emit m (d.directory pp lp)[i.val] (fun j => by
      rw [sched]; exact DataWriter.retained_record emit pub m shared frame output count sep (data ▸ i.isLt) (raw i) (fitted i) j)
  exact ⟨fun i => (fields i).2.1,fun i => (fields i).2.2.2.2.1⟩

/-- Field and writer facts at a real return of the complete data-plus-shared table. -/
structure PlacedImage (h : TeamHistory w) (d : Layout) (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → ℕ)
    (origin stride : ℕ) (pins : Pins.Layout) (cutoff : ℕ := origin) : Prop where
  /-- Actual consumer and tag columns. -/
  columns : DataColumns h.rows d pp lp owner origin stride
  /-- Actual sending team and source address. -/
  sources : SourceColumns h.rows d pp lp pins
  /-- The data prefix lies within the native loop count. -/
  count : (d.directory pp lp).length ≤ h.count
  /-- The start of the destination arena is a fitted address boundary. -/
  fits : cutoff ≤ 2^w
  /-- The consumer's absolute slot has its last writer at this data row. -/
  write : ∀ (i : Fin (d.directory pp lp).length) (j : Fin (d.directory pp lp)[i.val].width),
    LastWrite h.rows (h.rows i).teamB h.count i.val
      (if (h.rows i).teamA = (h.rows i).teamB then .dataHere else .receiveB) j.val
      (d.deliveredAt pp lp origin stride ⟨i,j⟩)
  /-- All processor and substituted inputs below the receiver arena survive. -/
  low : ∀ k < h.count, ∀ a < cutoff, (h.rows k).protectsCell h.team a

/-- The verified cell placement and actual native pair-row fields provide the
writer and preservation facts simultaneously for all consumers. -/
theorem PlacedImage.of_disjoint_layout {cutoff : ℕ} {h : TeamHistory w} {d : Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) {owner : ℕ → ℕ} (cols : DataColumns h.rows d pp lp owner origin stride)
    {pins : Pins.Layout} (sources : SourceColumns h.rows d pp lp pins)
    {g : Cube.SharedRows.Layout} (shared : g.LastWriteFields h.rows)
    (count : (d.directory pp lp).length = g.dataCount)
    (returned : h.count = g.dataCount+g.groups.choose 2)
    (disjoint : origin+cells*stride ≤ g.banks ∨ g.banks+g.stride*g.groups^2 ≤ origin)
    (dataRoom : origin+cells*stride ≤ 2^w) (cut : cutoff ≤ min origin g.banks) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w) :
    PlacedImage h d pp lp owner origin stride pins cutoff := by
  refine ⟨cols,sources,by omega,by have := cut.trans (min_le_left ..); omega,?_,?_⟩
  · intro i j
    rw [returned]
    exact placed_data_lastWrite_disjoint placement bound origin stride room hw cols shared count disjoint dataRoom capacity i j
  · intro k hk a ha
    exact placed_protects_below_banks placement bound origin stride room hw cols shared count dataRoom capacity
      (returned ▸ hk) h.team (ha.trans_le cut)

/-- Data-first specialization with protection up to the first receiving cell. -/
theorem PlacedImage.of_layout {h : TeamHistory w} {d : Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) {owner : ℕ → ℕ} (cols : DataColumns h.rows d pp lp owner origin stride)
    {pins : Pins.Layout} (sources : SourceColumns h.rows d pp lp pins)
    {g : Cube.SharedRows.Layout} (shared : g.LastWriteFields h.rows)
    (count : (d.directory pp lp).length = g.dataCount)
    (returned : h.count = g.dataCount+g.groups.choose 2)
    (disjoint : origin+cells*stride ≤ g.banks) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w) :
    PlacedImage h d pp lp owner origin stride pins :=
  of_disjoint_layout placement bound origin stride room hw cols sources shared count returned (Or.inl disjoint)
    (by omega) (le_min le_rfl (by omega)) capacity

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
