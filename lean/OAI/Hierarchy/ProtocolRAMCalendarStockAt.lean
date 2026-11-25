import OAI.Hierarchy.ProtocolRAMCalendarFeedLayout

namespace OAI
/-! # Chronological stock addresses at actual trials and virtual boundary endpoints -/

namespace Hierarchy.ProtocolRAM.Calendar

open AdaptiveProbe
variable {z d k N q goods : ℕ}

private theorem previous_same (c : Mesh) (initial : ℕ) (published : Event→ℕ) {e e' : Event}
    (same : position c e=position c e') : previousStock c initial published e=previousStock c initial published e' := by
  simp only [previousStock,same]

theorem previous_succ (c : Mesh) (initial : ℕ) (published : Event→ℕ) {e e' : Event}
    (inside : e∈events c) (next : position c e'=position c e+1) :
    previousStock c initial published e'=published e := by
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp inside
  have idx := position_at c hj
  rw [idx] at next
  simp only [previousStock,next,Nat.zero_lt_succ,true_and,show j+1≤(events c).length from hj,
    dite_true,Nat.add_sub_cancel]

noncomputable def stockAt (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods) (initial : ℕ)
    (a : Attempt) (i : Commodity (Fin (2^z)) N k) : ℕ :=
  previousStock c initial (publishedStock c arena format) (.attempt a)+PurchaseInventory.slot i

/-- An earlier stock word is safe even before the next attempt reads its own
frozen offer and runs its post scan. -/
theorem stockAt_below (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods) (initial : ℕ)
    (a : Attempt) (i : Commodity (Fin (2^z)) N k)
    (first : initial+PurchaseInventory.footprint z N k≤arena.first)
    (attempts : ∀ t,(format t).pricedArea.output+PurchaseInventory.footprint z N k≤arena.base c (.attempt t)+arena.stride)
    (feeds : PurchaseInventory.footprint z N k≤arena.stride) :
    stockAt c arena format initial a i<arena.base c (.attempt a) := by
  apply (Nat.add_lt_add_left (PurchaseInventory.slot_lt i) _).trans_le
  apply previous_before c arena initial _ (publishedStock c arena format) first _ (.attempt a)
  intro e
  cases e with
  | attempt t => exact attempts t
  | feed b => exact Nat.add_le_add_left feeds _

theorem stockAt_initial (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods) (initial : ℕ)
    (i : Commodity (Fin (2^z)) N k) :
    stockAt c arena format initial (.outer 0 0) i=initial+PurchaseInventory.slot i := by
  simp [stockAt,previousStock,position,trialBase]

theorem stockAt_outer_end (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial width cap p : ℕ) (i : Commodity (Fin (2^z)) N k) :
    stockAt c arena format initial (.outer p c.outerFuel) i=
      (FeedLayout.atEvent (N:=N) c arena format initial width cap (.outer p)).active+PurchaseInventory.slot i :=
  congrArg (·+PurchaseInventory.slot i) (previous_same c initial (publishedStock c arena format)
    (e:=.attempt (.outer p c.outerFuel)) (e':=.feed (.outer p)) rfl)

theorem stockAt_inner_end (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial width cap p a j : ℕ) (i : Commodity (Fin (2^z)) N k) :
    stockAt c arena format initial (.inner p a j c.innerFuel) i=
      (FeedLayout.atEvent (N:=N) c arena format initial width cap (.inner p a j)).active+PurchaseInventory.slot i :=
  congrArg (·+PurchaseInventory.slot i) (previous_same c initial (publishedStock c arena format)
    (e:=.attempt (.inner p a j c.innerFuel)) (e':=.feed (.inner p a j)) rfl)

theorem outerFeed_occurs (c : Mesh) {p : ℕ} (hp : p<c.inject+c.cool) :
    Event.feed (.outer p)∈events c := by
  exact List.mem_flatMap.mpr ⟨p,List.mem_range.mpr hp,List.mem_append_right _ (by simp)⟩

theorem innerFeed_occurs (c : Mesh) {p a j : ℕ} (hp : p<c.inject+c.cool) (ha : a<c.outerFuel)
    (hj : j<c.reserveSteps) : Event.feed (.inner p a j)∈events c := by
  apply List.mem_flatMap.mpr
  refine ⟨p,List.mem_range.mpr hp,List.mem_append_left _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨a,List.mem_range.mpr ha,List.mem_cons_of_mem _ ?_⟩
  exact List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,List.mem_append_right _ (by simp)⟩

theorem stockAt_outer_next (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial width cap p : ℕ) (i : Commodity (Fin (2^z)) N k) (hp : p<c.inject+c.cool) :
    stockAt c arena format initial (.outer (p+1) 0) i=
      (FeedLayout.atEvent (N:=N) c arena format initial width cap (.outer p)).kept+PurchaseInventory.slot i := by
  apply congrArg (·+PurchaseInventory.slot i)
  apply previous_succ c initial (publishedStock c arena format) (outerFeed_occurs c hp)
  simp [position,trialBase,phaseSize,Nat.add_mul,Nat.add_assoc]

theorem stockAt_inner_next (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial width cap p a j : ℕ) (i : Commodity (Fin (2^z)) N k)
    (hp : p<c.inject+c.cool) (ha : a<c.outerFuel) (hj : j<c.reserveSteps) :
    stockAt c arena format initial (.inner p a (j+1) 0) i=
      (FeedLayout.atEvent (N:=N) c arena format initial width cap (.inner p a j)).kept+PurchaseInventory.slot i := by
  apply congrArg (·+PurchaseInventory.slot i)
  apply previous_succ c initial (publishedStock c arena format) (innerFeed_occurs c hp ha hj)
  simp [position,sliceBase,sliceSize,Nat.add_mul,Nat.add_assoc]

theorem stockAt_entry (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial p a : ℕ) (i : Commodity (Fin (2^z)) N k) (hp : p<c.inject+c.cool) (ha : a<c.outerFuel) :
    stockAt c arena format initial (.inner p a 0 0) i=(format (.outer p a)).pricedArea.output+PurchaseInventory.slot i := by
  apply congrArg (·+PurchaseInventory.slot i)
  have inside : Event.attempt (.outer p a) ∈ events c := by
    exact List.mem_flatMap.mpr ⟨p,List.mem_range.mpr hp,List.mem_append_left _
      (List.mem_flatMap.mpr ⟨a,List.mem_range.mpr ha,List.mem_cons_self ..⟩)⟩
  apply previous_succ c initial (publishedStock c arena format) inside
  simp [position,sliceBase]

theorem stockAt_inner_after (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial p a j b : ℕ) (i : Commodity (Fin (2^z)) N k)
    (hp : p<c.inject+c.cool) (ha : a<c.outerFuel) (hj : j<c.reserveSteps) (hb : b<c.innerFuel) :
    stockAt c arena format initial (.inner p a j (b+1)) i=
      (format (.inner p a j b)).pricedArea.output+PurchaseInventory.slot i := by
  apply congrArg (·+PurchaseInventory.slot i)
  have inside : Event.attempt (.inner p a j b)∈events c := by
    apply List.mem_flatMap.mpr
    refine ⟨p,List.mem_range.mpr hp,List.mem_append_left _ ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨a,List.mem_range.mpr ha,List.mem_cons_of_mem _ ?_⟩
    apply List.mem_flatMap.mpr
    exact ⟨j,List.mem_range.mpr hj,List.mem_append_left _ (List.mem_map.mpr ⟨b,List.mem_range.mpr hb,rfl⟩)⟩
  apply previous_succ c initial (publishedStock c arena format) inside
  simp [position,Nat.add_assoc]

/-- The endpoint of the reserve loop and the next outer trial name precisely
the same active words, including a purchase with zero reserve intervals. -/
theorem stockAt_purchase_end (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial p a : ℕ) (i : Commodity (Fin (2^z)) N k) :
    stockAt c arena format initial (.inner p a c.reserveSteps 0) i=
      stockAt c arena format initial (.outer p (a+1)) i := by
  apply congrArg (·+PurchaseInventory.slot i)
  apply previous_same
  simp [position,sliceBase,trialBase,trialSize,Nat.add_mul,Nat.add_assoc]

end Hierarchy.ProtocolRAM.Calendar

end OAI
