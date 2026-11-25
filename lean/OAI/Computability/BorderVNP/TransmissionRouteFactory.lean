import OAI.Computability.BorderVNP.TransmissionRouteBank

/-! # Pre-scheduler layout certificates from the two native descriptor writers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM Transmission Packing.Directory Function
open private index_covered from OAI.Computability.BorderVNP.TransmissionSharedLastWrite

variable {w : ℕ}

/-- The incoming data and shared descriptors provide fitted routes and final-writer
facts at every genuine scheduler image and returning history. -/
structure WrittenPlacement (tab : TableLayout) (row : ℕ → TableRow) (before : Memory w)
    (pub : Arg → Word w) (d : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → ℕ)
    (origin stride : ℕ) (pins : Pins.Layout) : Prop where
  /-- Positive native word width. -/
  word : 0 < w
  /-- The populated data prefix precedes the end of the combined scheduler table. -/
  count : (d.directory pp lp).length ≤ tab.count
  /-- At least one processor supplies a data field. -/
  positive : 0 < d.processors
  /-- Physical input dimensions read by the data writer. -/
  dimensions : d.processors = pins.processors ∧ d.literal = pins.literal
  /-- Both arrays of actual data sources precede the cell banks. -/
  sourceRoom : pins.processors*pins.stride ≤ origin ∧ pins.ibase+pins.count ≤ origin
  /-- The final scheduler interval precedes all destination banks. -/
  after : tab.ordinals+tab.count ≤ origin
  /-- Full word room for all reached stores and sender reads. -/
  route : ∀ mt, tab.Image row (readings before) (readings mt) → RouteRanges tab pub mt
  /-- Actual raw source, destination, and width columns before the first transfer. -/
  columns : ∀ mt : Memory w, tab.Image row (readings before) (readings mt) →
    DataColumns (tableRange tab mt) d pp lp owner origin stride ∧ SourceColumns (tableRange tab mt) d pp lp pins
  /-- Appended symbol-pair rows have the native shared tag. -/
  sharedTag : ∀ mt : Memory w, tab.Image row (readings before) (readings mt) → ∀ i,
    (d.directory pp lp).length ≤ i → i < tab.count → (tableRange tab mt i).kind = 0
  /-- Every reached store of the installed table avoids the complete lower region. -/
  protects : ∀ mt : Memory w, tab.Image row (readings before) (readings mt) → ∀ i < tab.count, ∀ self a,
    a < tab.readExtent pins → (tableRange tab mt i).protectsCell self a
  /-- Data columns and actual final destinations at every native return. -/
  placed : ∀ h : TeamHistory w, h.rows = tableRange tab h.initial → h.count = tab.count →
    tab.Image row (readings before) (readings h.initial) → PlacedImage h d pp lp owner origin stride pins (tab.readExtent pins)

/-- Build the complete pre-scheduler certificate from the memory written by the
data lowering and the shared appender, together with the canonical cell slab placement.
The raw rows can be read directly using `DataWriter.demandAt_published`. -/
theorem WrittenPlacement.of_disjoint_writers {tab : TableLayout} {row : ℕ → TableRow} {before m : Memory w}
    (pub : Arg → Word w) (al : tab.Allocated w) (emit : DataWriter.Layout) (g : Cube.SharedRows.Layout)
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) (readings before))
    (fit : g.Fits w (readings (DataWriter.publish emit pub m)))
    (frame : g.frame = (pub 0).val) (output : g.records = emit.output)
    (sched : tab.records = emit.output) (count : g.dataCount = emit.count)
    (d : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → ℕ) (origin stride : ℕ)
    (data : (d.directory pp lp).length = emit.count) (total : tab.count = g.dataCount+g.groups.choose 2)
    (sep : (pub 0).val+13 < emit.output ∨ emit.output+emit.count*7 ≤ (pub 0).val+13)
    (raw : ∀ i : Fin (d.directory pp lp).length,
      DataWriter.demandAt (readings m) (emit.input+i.val*7) = (d.directory pp lp)[i.val])
    (fitted : ∀ i : Fin (d.directory pp lp).length,
      ∀ x ∈ DataWriter.record emit (readings m) (d.directory pp lp)[i.val], x < 2^w)
    (owners : ∀ i : Fin (d.directory pp lp).length,
      let cell := (d.directory pp lp)[i.val].cell
      readings m (emit.owners+cell*2) = owner cell ∧ readings m (emit.owners+cell*2+1) = origin+cell*stride)
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (room : ∀ c, DataSlabs.size cell width c ≤ stride) (hw : 0 < w)
    (processors : d.processors = emit.pins.processors) (literal : d.literal = emit.pins.literal)
    (input : emit.pins.processors*emit.pins.stride ≤ origin) (substitute : emit.pins.ibase+emit.pins.count ≤ origin)
    (after : tab.ordinals+tab.count ≤ origin)
    (disjoint : origin+cells*stride ≤ g.banks ∨ g.banks+g.stride*g.groups^2 ≤ origin)
    (dataRoom : origin+cells*stride ≤ 2^w) (readRoom : tab.readExtent emit.pins ≤ g.banks) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w) :
    WrittenPlacement tab row before pub d pp lp owner origin stride emit.pins := by
  have cut : tab.readExtent emit.pins ≤ min origin g.banks := by
    exact le_min (by unfold TableLayout.readExtent; omega) readRoom
  have sharedAfter := (tab.readExtent_bounds emit.pins).1.trans readRoom
  have full : emit.count ≤ tab.count := by omega
  have columns {mt : Memory w} (image : tab.Image row (readings before) (readings mt)) :=
    DataColumns.of_writers image al d pp lp owner origin stride emit pub m g shared frame output sched count
      data full sep raw fitted owners
  have sources {mt : Memory w} (image : tab.Image row (readings before) (readings mt)) :=
    SourceColumns.of_writers image al d pp lp emit pub m g shared frame output sched count data full sep raw fitted
  have recBase := sched.trans output.symm
  have cnt := data.trans count.symm
  refine ⟨hw,data.trans_le full,bound.processors,⟨processors,literal⟩,⟨input,substitute⟩,after,?_,?_,?_,?_,?_⟩
  · intro mt image
    exact RouteRanges.of_banks pub image al placement bound origin stride room hw (columns image) (sources image)
      processors literal input substitute shared fit recBase cnt total after sharedAfter dataRoom capacity
  · exact fun _ image => ⟨columns image,sources image⟩
  · intro mt image i lo hi
    obtain ⟨t,ht,s,hs,rfl⟩ := index_covered g (cnt ▸ lo) (total ▸ hi)
    exact Fin.ext (g.shared_range_fields image al recBase total shared.rows hs ht).1
  · intro mt image i hi self a ha
    have pairs := Cube.SharedRows.Layout.LastWriteFields.of_scheduled image al fit recBase total shared.rows
    exact placed_protects_below_banks placement bound origin stride room hw (columns image) pairs cnt dataRoom capacity
      (total ▸ hi) self (ha.trans_le cut)
  · intro h rows returned image
    have pairs := Cube.SharedRows.Layout.LastWriteFields.of_scheduled image al fit recBase total shared.rows
    apply PlacedImage.of_disjoint_layout placement bound origin stride room hw (rows ▸ columns image) (rows ▸ sources image)
      (rows ▸ pairs) cnt (returned.trans total) disjoint dataRoom cut capacity

/-- The layout with data cells first and pair banks last remains a special case. -/
theorem WrittenPlacement.of_writers {tab : TableLayout} {row : ℕ → TableRow} {before m : Memory w}
    (pub : Arg → Word w) (al : tab.Allocated w) (emit : DataWriter.Layout) (g : Cube.SharedRows.Layout)
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) (readings before))
    (fit : g.Fits w (readings (DataWriter.publish emit pub m)))
    (frame : g.frame = (pub 0).val) (output : g.records = emit.output)
    (sched : tab.records = emit.output) (count : g.dataCount = emit.count)
    (d : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → ℕ) (origin stride : ℕ)
    (data : (d.directory pp lp).length = emit.count) (total : tab.count = g.dataCount+g.groups.choose 2)
    (sep : (pub 0).val+13 < emit.output ∨ emit.output+emit.count*7 ≤ (pub 0).val+13)
    (raw : ∀ i : Fin (d.directory pp lp).length,
      DataWriter.demandAt (readings m) (emit.input+i.val*7) = (d.directory pp lp)[i.val])
    (fitted : ∀ i : Fin (d.directory pp lp).length,
      ∀ x ∈ DataWriter.record emit (readings m) (d.directory pp lp)[i.val], x < 2^w)
    (owners : ∀ i : Fin (d.directory pp lp).length,
      let cell := (d.directory pp lp)[i.val].cell
      readings m (emit.owners+cell*2) = owner cell ∧ readings m (emit.owners+cell*2+1) = origin+cell*stride)
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (room : ∀ c, DataSlabs.size cell width c ≤ stride) (hw : 0 < w)
    (processors : d.processors = emit.pins.processors) (literal : d.literal = emit.pins.literal)
    (input : emit.pins.processors*emit.pins.stride ≤ origin) (substitute : emit.pins.ibase+emit.pins.count ≤ origin)
    (after : tab.ordinals+tab.count ≤ origin)
    (disjoint : origin+cells*stride ≤ g.banks) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w) :
    WrittenPlacement tab row before pub d pp lp owner origin stride emit.pins :=
  of_disjoint_writers pub al emit g shared fit frame output sched count d pp lp owner origin stride data total sep
    raw fitted owners placement bound room hw processors literal input substitute after (Or.inl disjoint)
    (by omega) (by unfold TableLayout.readExtent; omega) capacity

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
