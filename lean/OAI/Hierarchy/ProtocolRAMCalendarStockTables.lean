import OAI.Hierarchy.ProtocolRAMCalendarStockActual
import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceFormat

namespace OAI
/-! # Stock-step ports and half-table words from the original public tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockBound
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe PurchaseStage StockCommit
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {w z d k q goods r edges N : ℕ}

theorem prefix_low (C : Chart w q goods) (start : Memory w) (j cut : ℕ)
    (ran : mounted C ((events C.mesh).take j) start) (safe : ∀e∈events C.mesh,∀x< cut,outside C x e) :
    ∀x< cut,state C start j x=start x := by
  intro x hx
  apply run_outside C _ start x ran
  exact fun e he=>safe e (List.mem_of_mem_take he) x hx

theorem prefix_half (C : Chart w q goods) (start fixture : Memory w) (j : ℕ) (table : Bank)
    (ran : mounted C ((events C.mesh).take j) start)
    (safe : ∀e∈events C.mesh,∀x< table.base+table.size,outside C x e)
    (rom : ∀x,table.base≤ x→x< table.base+table.size→start x=FeedROM.halfAdvice table fixture x) :
    ∀x,table.base≤ x→x< table.base+table.size→state C start j x=FeedROM.halfAdvice table fixture x :=
  fun x lo hi=>(prefix_low C start j _ ran safe x hi).trans (rom x lo hi)

/-- The fixed occurrence table survives the chronological prefix, the current
frozen purchase and its guard, and the native label and seed writes. -/
theorem priced_ports (c : Mesh) (finish : ℝ) (price : PhasePrice) (f : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr)
    (ids : Attempt→Fin goods→Expr) (a : Attempt) (header : ℕ) (start : Memory (Native.wordBits z d Native.copies)) :
    let p := f a
    let h := p.occurrenceHeader header
    let g := p.labelSource sink idBase (role a) (ids a)
    let C := pricedInstalled c finish price f feeds sink idBase role ids
    let j := position c (.attempt a)
    let m := state C start j
    let L := C.layout a
    let B := repair C a
    h.Loaded start → p.withOccurrenceHeader header=p → p.occurrences=h.count →
    mounted C ((events c).take j) start → ready C (.attempt a) m →
    (∀e∈events c,∀x< h.stop,outside C x e) → (∀x< h.stop,protected C x (.attempt a)) →
    h.stop≤ g.out → g.out≤ p.pricedArea.start → goods≤2^Native.wordBits z d Native.copies →
    q≤2^Native.wordBits z d Native.copies → p.histMass<2^Native.wordBits z d Native.copies →
    q*p.histMass<2^Native.wordBits z d Native.copies →
    Nonempty (PortPlan (fresh p.pricedArea p.stockSource) (enabledBatch L B)
      (stageInput p.pricedArea p.stockSource g (postOutput L B (prepared C a m))) L.candidates) := by
  intro p h g C j m L B loaded sealed count ran ready below guard headerSpan labelSpan dFit qFit mass sumFit
  let post := postOutput L B (prepared C a m)
  have origin : h.Loaded m := loaded.frame (fun x _ hi=>prefix_low C start j h.stop ran below x hi)
  have atPost : h.Loaded post := origin.frame (fun x _ hi=>postOutput_prior C a m x ready (guard x hi))
  have before := p.occurrenceLoaded header g post atPost headerSpan labelSpan
  have plan := p.occurrencePlan header _ count before dFit qFit mass sumFit
  rw [sealed] at plan
  exact ⟨plan⟩

/-- The source tables are read once on the initial booted tape. Each attempt
may have its own public occurrence header and share the division table. -/
structure Original (p : Format z d k q goods) (g : LabelSource) (head floor : ℕ)
    (start fixture : Memory w) : Prop where
  sealed : p.withOccurrenceHeader head=p
  count : p.occurrences=(p.occurrenceHeader head).count
  header : (p.occurrenceHeader head).Loaded start
  headLow : (p.occurrenceHeader head).stop≤ floor
  halfLow : p.stockSource.half.base+p.stockSource.half.size≤ floor
  preLabels : (p.occurrenceHeader head).stop≤ g.out
  digits : goods≤2^w
  terms : q≤2^w
  copies : p.histMass<2^w
  mass : q*p.histMass<2^w
  half : ∀x,p.stockSource.half.base≤ x→x< p.stockSource.half.base+p.stockSource.half.size→
    start x=FeedROM.halfAdvice p.stockSource.half fixture x

theorem trial_data (c : Mesh) (finish : ℝ) (price : PhasePrice) (f : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr)
    (ids : Attempt→Fin goods→Expr) (a : Attempt) (cap width first cutoff head : ℕ)
    (start fixture : Memory (Native.wordBits z d Native.copies)) :
    let p := f a
    let g := p.labelSource sink idBase (role a) (ids a)
    let C := pricedInstalled c finish price f feeds sink idBase role ids
    let j := position c (.attempt a)
    let m := state C start j
    TrialLayout C a p.pricedArea p.stockSource g cap width cutoff → Original p g head first start fixture →
    (∀e,∀u< first,protected C u e ∧ outside C u e) → mounted C ((events c).take j) start →
    ready C (.attempt a) m → TrialData C a m fixture p.pricedArea p.stockSource g cap width cutoff := by
  intro p g C j m layout rom floor ran fit
  refine ⟨layout,?_,?_⟩
  · exact priced_ports c finish price f feeds sink idBase role ids a head start rom.header rom.sealed rom.count
      ran fit (fun e _ x hi=>(floor e x (hi.trans_le rom.headLow)).2)
      (fun x hi=>(floor (.attempt a) x (hi.trans_le rom.headLow)).1)
      rom.preLabels layout.window.label rom.digits rom.terms rom.copies rom.mass
  · exact prefix_half C start fixture j p.stockSource.half ran
      (fun e _ x hi=>(floor e x (hi.trans_le rom.halfLow)).2) rom.half

/-- From static address certificates and the original CPU tables, chronological
readiness with bounded inputs produces a mounted capped run. -/
theorem priced_static (c : Mesh) (finish : ℝ) (prices : PhasePrice) (arena : Arena)
    (shape F : Attempt→Format z d k q goods) (initial zeroReserve width cap : ℕ) (sink : Sink r edges)
    (idBase : ℕ) (head : Attempt→ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (start fixture : Memory (Native.wordBits z d Native.copies))
    (empty : ∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock initial start i=0)
    (vacant : ∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock zeroReserve start i=0)
    (first : initial+PurchaseInventory.footprint z N k≤ arena.first)
    (zeroSpan : zeroReserve+PurchaseInventory.footprint z N k≤ arena.first)
    (place : ∀a,arena.base c (.attempt a)≤ (F a).market.failures.base ∧ arena.base c (.attempt a)≤ (F a).market.shelf.firstBase ∧
      arena.base c (.attempt a)≤ (F a).testsStart)
    (area : ∀a,(F a).pricedArea=(shape a).pricedArea)
    (keys : ∀a,PurchaseInventory.footprint z N k≤ (F a).pricedArea.goods)
    (postSpan : ∀a,(shape a).pricedArea.output+(shape a).pricedArea.goods+PurchaseInventory.footprint z N k≤
      arena.base c (.attempt a)+arena.stride)
    (feedSpan : PurchaseInventory.footprint z N k≤ arena.stride)
    (capFits : cap*width<2^Native.wordBits z d Native.copies) :
    let b := pricedBanks c arena shape initial zeroReserve
    let feeds := feedColumns (N:=N) c arena shape initial width cap
    let C := pricedInstalled c finish prices F feeds sink idBase role ids
    (∀a,(F a).stockSource.old.base=b.previous c (.attempt a) ∧ (F a).stockSource.reserve.base=b.reserve (.attempt a)) →
    (∀f,Event.feed f∈events c → (FeedLayout.atEvent (N:=N) c arena shape initial width cap f).Before c C.modeAt f ∧
      (FeedLayout.atEvent (N:=N) c arena shape initial width cap f).stop<2^Native.wordBits z d Native.copies) →
    (∀a, Event.attempt a∈events c →
      let f := F a
      let g := f.labelSource sink idBase (role a) (ids a)
      TrialLayout C a f.pricedArea f.stockSource g cap width (arena.base c (.attempt a)) ∧
        Original f g (head a) arena.first start fixture) →
    (∀a, Event.attempt a∈events c →
      let j := position c (.attempt a)
      let m := state C start j
      mounted C ((events c).take j) start → Bounded z N k (b.previous c (.attempt a)) (cap*width) m →
      Bounded z N k (b.reserve (.attempt a)) (cap*width) m → ready C (.attempt a) m) →
    Run C b start z N k (cap*width) := by
  intro b feeds C pointer feed descriptors reachable
  apply priced c finish prices arena shape F initial zeroReserve width cap sink idBase role ids start fixture
    empty vacant first zeroSpan place area keys postSpan feedSpan capFits pointer feed
  intro a live m ran old saved
  have ready := reachable a live ran old saved
  obtain ⟨layout,origin⟩ := descriptors a live
  refine ⟨ready,trial_data c finish prices F feeds sink idBase role ids a cap width arena.first
    (arena.base c (.attempt a)) (head a) start fixture layout origin ?_ ran ready⟩
  intro e addr low
  have base : arena.first≤ arena.base c e := Nat.le_add_right ..
  exact priced_event_floor_with (N:=N) c finish prices arena shape F initial width cap sink idBase role ids
    place e addr (low.trans_le base)

end Hierarchy.ProtocolRAM.Calendar.StockBound
end

end OAI
