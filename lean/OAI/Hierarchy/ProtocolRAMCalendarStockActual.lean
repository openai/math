import OAI.Hierarchy.ProtocolRAMCalendarStockBound
import OAI.Hierarchy.ProtocolRAMCalendarStockStepBound
import OAI.Hierarchy.ProtocolRAMCalendarFeedLifetime

namespace OAI
/-! # Native stock cap from priced post, capped feed, and chronological archives -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockBound
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe PurchaseStage StockCommit
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {z N d k q goods r edges w : ℕ}

def pricedBanks (c : Mesh) (arena : Arena) (shape : Attempt→Format z d k q goods) (initial zeroReserve : ℕ) : Banks :=
  ⟨initial,zeroReserve,publishedStock c arena shape,fun a=>(shape a).pricedArea.output+(shape a).pricedArea.goods⟩

/-- The public address and width certificate for a concrete clipped stock update. -/
structure TrialLayout (C : Chart w q goods) (x : Attempt) (a : Area) (s : Sources)
    (g : LabelSource) (cap width cutoff : ℕ) : Prop where
  window : StockWindow a s g (C.modeAt x) (cap*width) w
  inputs : PrefixFits a s (enabledBatch (C.layout x) (repair C x))
  space : MaskSpace (C.layout x) (repair C x)
  board : Board (C.layout x) (repair C x) w
  positive : 0< (C.layout x).candidates
  padded : (C.layout x).candidates≤ (repair C x).repairBits.size
  padBefore : (repair C x).repairBits.base+(C.layout x).candidates≤ g.out
  oldLow : s.old.base+a.goods≤ cutoff
  savedLow : s.reserve.base+a.goods≤ cutoff
  halfLow : s.half.base+s.half.size≤ cutoff

/-- The port directory and the half table at the actual chronological memory. -/
structure TrialData (C : Chart w q goods) (x : Attempt) (m fixture : Memory w) (a : Area) (s : Sources)
    (g : LabelSource) (cap width cutoff : ℕ) : Prop extends TrialLayout C x a s g cap width cutoff where
  ports : let B := repair C x
    let L := C.layout x
    let post := postOutput L B (prepared C x m)
    Nonempty (PortPlan (fresh a s) (enabledBatch L B) (stageInput a s g post) L.candidates)
  half : ∀i,s.half.base≤ i→i< s.half.base+s.half.size→m i=FeedROM.halfAdvice s.half fixture i

/-- All chronological stock, including each future frozen trial and its inner
reserve row. The induction starts at the two zero banks and uses the
installed clipping, half and hold operations at each native event. -/
theorem priced (c : Mesh) (finish : ℝ) (prices : PhasePrice) (arena : Arena)
    (shape F : Attempt→Format z d k q goods) (initial zeroReserve width cap : ℕ) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (start fixture : Memory (Native.wordBits z d Native.copies))
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
      let m := state C start (position c (.attempt a))
      mounted C ((events c).take (position c (.attempt a))) start →
      Bounded z N k (b.previous c (.attempt a)) (cap*width) m → Bounded z N k (b.reserve (.attempt a)) (cap*width) m →
      ready C (.attempt a) m ∧ TrialData C a m fixture (F a).pricedArea (F a).stockSource ((F a).labelSource sink idBase (role a) (ids a))
        cap width (arena.base c (.attempt a))) → Run C b start z N k (cap*width) := by
  intro b feeds C pointer feedReady trialReady
  have protectedLow (e : Event) (p : ℕ) (hi : p< arena.base c e) : protected C p e ∧ outside C p e :=
    priced_event_floor_with (N:=N) c finish prices arena shape F initial width cap sink idBase role ids place e p hi
  apply chronological C arena b start z N k (cap*width) empty vacant first zeroSpan
  · intro e _ base hb
    cases e with
    | attempt a =>
      have endAt := postSpan a
      simp only [b,pricedBanks,Banks.publications,publishedStock,List.mem_cons,List.not_mem_nil,or_false] at hb
      change base+PurchaseInventory.footprint z N k ≤ arena.base c (.attempt a)+arena.stride
      rcases hb with rfl|rfl <;> omega
    | feed f =>
      have eq : base=arena.base c (.feed f) := List.mem_singleton.mp hb
      rw [eq];exact Nat.add_le_add_left feedSpan _
  · exact fun e _ p hp=>(protectedLow e p hp).2
  · intro u
    let m := state C start u.val
    let e := (events c)[u.val]
    have live : e∈events c := List.getElem_mem _
    have eqn : position c e=u.val := position_at c u.isLt
    change mounted C ((events c).take u.val) start → Bounded z N k (b.previous c e) (cap*width) m → Bounded z N k (b.reserve e) (cap*width) m →
      ready C e m ∧ ∀base∈b.publications e,Bounded z N k base (cap*width) (after C e m)
    intro ran active held
    cases event : e with
    | feed f =>
      let L := FeedLayout.atEvent (N:=N) c arena shape initial width cap f
      obtain ⟨before,room⟩ := feedReady f (event▸live)
      refine ⟨L.ready C f m rfl before room,?_⟩
      intro base hb i
      obtain rfl := List.mem_singleton.mp hb
      exact L.bounded C f m rfl before room capFits i
    | attempt a =>
      simp only [event] at live eqn active held
      have prereq := trialReady a live
      rw [eqn] at prereq
      obtain ⟨can,rec⟩ := prereq ran active held
      refine ⟨can,?_⟩
      let A := (F a).pricedArea
      let s := (F a).stockSource
      let g := (F a).labelSource sink idBase (role a) (ids a)
      have two (i : Commodity (Fin (2^z)) N k) :
          (after C (.attempt a) m (A.output+PurchaseInventory.slot i)).val≤ cap*width ∧
          (after C (.attempt a) m (A.output+A.goods+PurchaseInventory.slot i)).val≤ cap*width := by
        let p : Fin A.goods := ⟨_,(PurchaseInventory.slot_lt i).trans_le (keys a)⟩
        have protectedAt (x : ℕ) (hi : x< arena.base c (.attempt a)) := (protectedLow (.attempt a) x hi).1
        apply StockCommit.post_bounded C a m A s g fixture p cap width rec.window can rfl rec.inputs rec.space rec.board rec.positive rec.padded rec.padBefore (Classical.choice rec.ports)
        · exact protectedAt _ ((Nat.add_lt_add_left p.isLt s.old.base).trans_le rec.oldLow)
        · exact protectedAt _ ((Nat.add_lt_add_left p.isLt s.reserve.base).trans_le rec.savedLow)
        · exact fun i _ hi=>protectedAt _ (hi.trans_le rec.halfLow)
        · exact rec.half
        · change (m ((F a).stockSource.old.base+PurchaseInventory.slot i)).val≤ _
          rw [(pointer a).1];exact active i
        · change (m ((F a).stockSource.reserve.base+PurchaseInventory.slot i)).val≤ _
          rw [(pointer a).2];exact held i
      intro base hb i
      simp only [b,pricedBanks,Banks.publications,publishedStock,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl
      · simpa only [PurchaseInventory.stock,A,area a] using (two i).1
      · simpa only [PurchaseInventory.stock,A,area a] using (two i).2

end Hierarchy.ProtocolRAM.Calendar.StockBound
end

end OAI
