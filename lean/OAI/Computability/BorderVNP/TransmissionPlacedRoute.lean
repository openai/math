import OAI.Computability.BorderVNP.TransmissionDeliveryReturns
import OAI.Computability.BorderVNP.DiagonalNativeRoute

/-! # Complete native routes entering and returning from the allocated cell banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM Transmission Packing.Directory Function
open private index_covered from OAI.Computability.BorderVNP.TransmissionSharedLastWrite
open private route_iff from OAI.Computability.BorderVNP.DiagonalNativeRoute

variable {w : ℕ}

/-- Resource conditions for the native route follow from the true populated
literal/pin rows, appended symbol pairs, and separated fitted address arenas.
The proof is available before constructing any transmission return. -/
theorem RouteRanges.of_banks {tab : TableLayout} {row : ℕ → TableRow} {before src : ℕ → ℕ}
    {m : Memory w} (pub : Arg → Word w) (image : tab.Image row before (readings m)) (al : tab.Allocated w)
    {d : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) {owner : ℕ → ℕ} (cols : DataColumns (tableRange tab m) d pp lp owner origin stride)
    {pins : Pins.Layout} (sources : SourceColumns (tableRange tab m) d pp lp pins)
    (processors : d.processors = pins.processors) (literal : d.literal = pins.literal)
    (input : pins.processors*pins.stride ≤ origin) (substitute : pins.ibase+pins.count ≤ origin)
    {g : Cube.SharedRows.Layout} (shared : g.Emitted src before) (fit : g.Fits w src)
    (records : tab.records = g.records) (count : (d.directory pp lp).length = g.dataCount)
    (total : tab.count = g.dataCount+g.groups.choose 2) (after : tab.ordinals+tab.count ≤ origin)
    (sharedAfter : tab.ordinals+tab.count ≤ g.banks) (dataRoom : origin+cells*stride ≤ 2^w) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w) :
    RouteRanges tab pub m := by
  have sharedFields := Cube.SharedRows.Layout.LastWriteFields.of_scheduled image al fit records total shared.rows
  constructor
  · intro k hk r self mode sel reg dest
    by_cases data : k < (d.directory pp lp).length
    · obtain ⟨lo,hi⟩ := data_destination_bounds placement bound origin stride room hw cols ⟨k,data⟩
        (directoryFrame pub m 0) mode sel reg dest
      exact ⟨after.trans lo,hi.trans dataRoom⟩
    · obtain ⟨lo,hi⟩ := shared_destination_bounds sharedFields capacity k (by omega) (total ▸ hk)
        (directoryFrame pub m 0) mode reg dest
      exact ⟨sharedAfter.trans lo,hi⟩
  · intro k hk r _
    by_cases data : k < (d.directory pp lp).length
    · let i : Fin (d.directory pp lp).length := ⟨k,data⟩
      let r := (d.directory pp lp)[i.val]
      have pos : 0 < r.width := of_decide_eq_true (List.mem_filter.mp (List.getElem_mem i.isLt :
        r ∈ d.directory pp lp)).2
      have hi := d.source_below pp lp (List.getElem_mem i.isLt) bound.processors
        (Nat.sub_lt pos (by decide : 0 < 1)) pins processors literal origin input substitute
      change (tableRange tab m i).source.val+(tableRange tab m i).width.val ≤ 2^w
      rw [sources.source i,cols.width i]
      change r.sourceBase pins+(r.width-1) < origin at hi
      change r.sourceBase pins+r.width ≤ _
      omega
    · obtain ⟨t,ht,s,hs,rfl⟩ := index_covered g (by omega : g.dataCount ≤ k) (total ▸ hk)
      have zero := (g.shared_range_fields image al records total shared.rows hs ht).2.2.2.2.1
      rw [zero,Nat.zero_add]
      exact (tableRange tab m _).width.isLt.le

/-- The data-first physical placement specializes the independent bank bounds. -/
theorem RouteRanges.of_placed {tab : TableLayout} {row : ℕ → TableRow} {before src : ℕ → ℕ}
    {m : Memory w} (pub : Arg → Word w) (image : tab.Image row before (readings m)) (al : tab.Allocated w)
    {d : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) {owner : ℕ → ℕ} (cols : DataColumns (tableRange tab m) d pp lp owner origin stride)
    {pins : Pins.Layout} (sources : SourceColumns (tableRange tab m) d pp lp pins)
    (processors : d.processors = pins.processors) (literal : d.literal = pins.literal)
    (input : pins.processors*pins.stride ≤ origin) (substitute : pins.ibase+pins.count ≤ origin)
    {g : Cube.SharedRows.Layout} (shared : g.Emitted src before) (fit : g.Fits w src)
    (records : tab.records = g.records) (count : (d.directory pp lp).length = g.dataCount)
    (total : tab.count = g.dataCount+g.groups.choose 2) (after : tab.ordinals+tab.count ≤ origin)
    (disjoint : origin+cells*stride ≤ g.banks) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w) :
    RouteRanges tab pub m :=
  of_banks pub image al placement bound origin stride room hw cols sources processors literal input substitute
    shared fit records count total after (by omega) (by omega) capacity

/-- An arbitrary return of the complete native route supplies a true transmission
history at exactly the memory produced by scheduling, successful relay and padding
checks, and precisely the same final words and chronological guesses. -/
theorem route_history_of_return (l : TableLayout) (row : ℕ → TableRow) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (al : l.Allocated w) (ordered : l.Ordered) (rowsFit : l.RowsFit w row)
    (hf : (pub 0).val = l.frame) (loaded : l.frameFields (readings m)) (initial : l.recordsMatch row (readings m))
    (f : BroadcastFrame) (im : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (teams : f.teams = l.teams)
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity)
    (safe : ∀ mt, l.Image row (readings m) (readings mt) → RouteRanges l pub mt)
    (z : Returns route pub mac s m) :
    ∃ h : TeamHistory w, h.pub = pub ∧ h.macros = mac ∧ h.rows = tableRange l h.initial ∧
      h.count = l.count ∧ l.Image row (readings m) (readings h.initial) ∧ routingChecks l row f pub fit teams h.initial ∧
      h.history.val.2 = z.val.2 ∧ h.history.val.1.flatMap TeamRAM.Event.choices = z.val.1.flatMap TeamRAM.Event.choices ∧
      ∃ log t, Runs pub mac scheduleTable s m log t h.initial := by
  obtain ⟨⟨log,endBank,endMem⟩,full⟩ := z
  obtain ⟨start,entry,pre,tail,rfl,setup,transmit⟩ := Runs.seq_iff.mp (route_iff.mp full)
  obtain ⟨mid,scheduled,ss,cc,rfl,sched,chk⟩ := Runs.seq_iff.mp setup
  obtain ⟨_,_,_,canonical,_,_,image⟩ := scheduleTable_image pub mac s m l row al rowsFit hf loaded initial
  obtain ⟨rfl,rfl,rfl⟩ := sched.unique_of_deterministic (by decide) canonical
  change l.Image row (readings m) (readings scheduled) at image
  have checked := (route_checks pub mac mid scheduled image al ordered rowsFit hf loaded f im fit teams capacity).sound chk
  obtain ⟨rfl,pass⟩ := checked
  have ranges := safe _ image
  obtain ⟨E,eff⟩ := image_sender_equiv image al rowsFit initial pub mac start hf loaded f
    (image.broadcast_of_ordered ordered hf im) fit teams capacity
    (fun i hi => Range.directorySeparated_of_ordered ordered _ _ (ranges.destinations i hi))
    (fun i hi => teams ▸ Range.scheduleSeparated_of_ordered image ordered pub hf loaded _ _ (ranges.destinations i hi))
    ranges.sources
  have ct := image_count image al pub hf loaded
  let h := TeamHistory.ofEquiv (tableRange l entry) pub mac entry start E
    (fun b => ⟨(eff b).1,((eff b).2.1).trans (congrArg (tableMemory _ _ _ _ _) ct.symm)⟩) ⟨(tail,endBank,endMem),transmit⟩
  refine ⟨h,rfl,rfl,rfl,ct,image,pass,rfl,?_,⟨_,_,sched⟩⟩
  change tail.flatMap TeamRAM.Event.choices = ((ss++cc)++tail).flatMap TeamRAM.Event.choices
  rw [List.flatMap_append,Pins.noChoices (sched.seq chk) (by decide),List.nil_append]

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
