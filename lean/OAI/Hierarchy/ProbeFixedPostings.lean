import OAI.Hierarchy.ProbeFixedPostedBills
import OAI.Hierarchy.ProtocolRAMCalendarFeedLifetime
import OAI.Hierarchy.ProtocolRAMCalendarPricedPosting
import OAI.Hierarchy.ProtocolRAMCalendarSignedHistory

namespace OAI
/-! # Chronological increment of the actual fixed protocol's signed bill -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockCommit
open scoped BigOperators Classical

/-- All the geometric labels, flags, and packet choice keys used by a paid event
are allocated before the end of that event's stock-commit region. -/
theorem Format.chargeColumns {z d k q g : ℕ} (f : Format z d k q g) :
    f.labelStart + f.pricedArea.occurrences ≤ f.pricedArea.stop ∧
    f.board.reportOut 6+f.pricedArea.rows ≤ f.pricedArea.stop ∧
    f.board.purchaseOut+f.pricedArea.rows ≤ f.pricedArea.stop ∧
    f.board.boughtFields 5+f.pricedArea.rows ≤ f.pricedArea.stop ∧ 0<f.pricedArea.stop := by
  have endBound : f.pricedArea.start ≤ f.pricedArea.stop := by
    unfold Area.stop Area.output Area.excess Area.clip Area.src Area.broadcast Area.direct
    omega
  change f.board.verdict+1+f.occurrences≤f.pricedArea.stop at endBound
  have before (j : ℕ) (hj : j<17) :
      PostLayout.column f.maskStart f.indexBits f.market.rows j + f.market.rows ≤ f.board.verdict := by
    change PostLayout.column _ _ _ j + f.market.rows ≤
      PostLayout.column f.maskStart f.indexBits f.market.rows (17+3*g+f.checkedBoard.batch.quotes.length)
    have ord : j+1≤17+3*g+f.checkedBoard.batch.quotes.length := by omega
    have bound:=Nat.mul_le_mul_right f.market.rows ord
    rw [Nat.succ_mul] at bound
    unfold PostLayout.column
    omega
  exact ⟨endBound,(before 9 (by decide)).trans (by omega),(before 1 (by decide)).trans (by omega),
    (before 15 (by decide)).trans (by omega),by omega⟩

namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "S" => CoreBoard.Stages z (2^v.W)

private theorem posted_stop_congr {n d k' q' ports : ℕ} (b c : Format n d k' q' ports)
    (quotes : b.batch.batch.quotes.length=c.batch.batch.quotes.length)
    (flags : b.market.flags=c.market.flags) (rows : b.market.rows=c.market.rows)
    (excess : b.batch.tests.excess.rows=c.batch.tests.excess.rows)
    (payload : b.batch.tests.payload.rows=c.batch.tests.payload.rows)
    (failed : b.market.failures.rows=c.market.failures.rows)
    (bits : b.indexBits=c.indexBits) (occ : b.occurrences=c.occurrences)
    (goods : b.coordinates=c.coordinates) : b.pricedArea.stop=c.pricedArea.stop := by
  have mask : b.maskStart=c.maskStart := by
    change b.market.flags+b.market.rows+1+(b.batch.tests.excess.rows+1)+(b.batch.tests.payload.rows+1)+
      (b.market.failures.rows+1)=c.market.flags+c.market.rows+1+(c.batch.tests.excess.rows+1)+
      (c.batch.tests.payload.rows+1)+(c.market.failures.rows+1)
    rw [flags,rows,excess,payload,failed]
  let address (m i r o g digits : ℕ) :=
    (StockCommit.Area.mk (PostLayout.column m i r (17+3*ports+digits)+1+o) r o g 0).stop
  change address b.maskStart b.indexBits b.market.rows b.occurrences b.coordinates
      b.batch.batch.quotes.length = address c.maskStart c.indexBits c.market.rows c.occurrences
      c.coordinates c.batch.batch.quotes.length
  rw [mask,bits,rows,occ,goods,quotes]

/- Numeric address fields of the allocated slab and of its fully rebound program.
Giving both boards the same explicit scalar target keeps the comparison independent
of their distinct expressions and stock-source histories. -/
set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
private theorem posted_scalar_layout (native : Bool) (a : Attempt) :
    let seed:=v.seed P z width
    let sized:=v.sized seed width
    let slab:=v.slab seed P width
    let arena:=v.privateArena P z width
    let b:=if native then v.nativeBoards P z width else v.located seed P width
    let f:=build F b a P.joint.initial
    f.market.flags=Slab.flags slab sized (arena.base v.mesh (.attempt a)) ∧
    f.market.rows=Slab.rows sized ∧
    f.batch.tests.excess.rows=Slab.goods z (2^v.W) k ∧
    f.batch.tests.payload.rows=Slab.goods z (2^v.W) k ∧
    f.market.failures.rows=Slab.rows sized ∧
    f.indexBits=z+Slab.rowFactor sized ∧
    f.occurrences=Slab.rows sized*max (Fintype.card (StripDirectory.PayloadRole S k))
      (Fintype.card (StripDirectory.PurchasedRole v.depth k)) ∧
    f.coordinates=Slab.goods z (2^v.W) k := by
  dsimp only
  simp only [Slab.rows_eq]
  cases native <;> cases a <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
theorem attempt_room (a : Attempt) :
    (v.nativeFormats P z width a).pricedArea.stop ≤
      (v.privateArena P z width).base v.mesh (.attempt a)+(v.privateArena P z width).stride := by
  let seed:=v.seed P z width
  let allocated:=v.located seed P width
  let loaded:=v.nativeBoards P z width
  let arena:=v.privateArena P z width
  have fixed {letters : ℕ} (s : StripChart.Boards z (2^v.W) k letters v.depth) :=
    congrArg StockCommit.Area.stop (live_area v.mesh arena P.joint.initial (build F s)
      (fun e addr=>capacity F s e addr P.joint.initial) a)
  have quotes : (build F loaded a P.joint.initial).batch.batch.quotes.length =
      (build F allocated a P.joint.initial).batch.batch.quotes.length := by
    cases a with
    | outer phase trial =>
      change (List.ofFn (n:=Fintype.card (PayloadStrip.Quotes S k)) _).length =
        (List.ofFn (n:=Fintype.card (PayloadStrip.Quotes S k)) _).length
      simp only [List.length_ofFn]
    | inner phase trial window tick =>
      change (List.ofFn (n:=Fintype.card (ChainStrip.Axes v.depth k)) _).length =
        (List.ofFn (n:=Fintype.card (ChainStrip.Axes v.depth k)) _).length
      simp only [List.length_ofFn]
  have same : (build F loaded a P.joint.initial).pricedArea.stop =
      (build F allocated a P.joint.initial).pricedArea.stop := by
    obtain ⟨f,r,x,p,h,b,o,g⟩:=posted_scalar_layout v P z width true a
    obtain ⟨f',r',x',p',h',b',o',g'⟩:=posted_scalar_layout v P z width false a
    exact posted_stop_congr _ _ quotes (f.trans f'.symm) (r.trans r'.symm)
      (x.trans x'.symm) (p.trans p'.symm) (h.trans h'.symm) (b.trans b'.symm)
      (o.trans o'.symm) (g.trans g'.symm)
  exact ((fixed loaded).trans (same.trans (fixed allocated).symm)).le.trans
    (Slab.fit (v.slab seed P width) (v.sized seed width) F v.mesh P.joint.initial a)

theorem feed_room : 2*PurchaseInventory.footprint z S k ≤ (v.privateArena P z width).stride := by
  change 2*PurchaseInventory.footprint z S k ≤ _+8*PurchaseInventory.footprint z S k+4
  omega

/-- For each prefix the native bill words are all contained in that prefix's
private arena interval, including the actual born-link fee and length stamps. -/
theorem issued_room (e : Event) :
    (v.issued P z width r banks src tab dst owners e).Below
      ((v.privateArena P z width).base v.mesh e+(v.privateArena P z width).stride) := by
  cases e with
  | attempt a =>
    let f:=v.nativeFormats P z width a
    have bounds:=f.chargeColumns
    have finish:=v.attempt_room P z width a
    apply reportedRows_below
    · exact finish
    · exact bounds.1.trans finish
    · exact bounds.2.1.trans finish
    · exact fun _=>bounds.2.2.2.2.trans_le finish
    · exact bounds.2.2.1.trans finish
    · exact bounds.2.2.2.1.trans finish
  | feed b =>
    let A:=v.privateArena P z width
    have bound : 2*PurchaseInventory.footprint z S k ≤ A.stride := v.feed_room P z width
    have positive : 0<PurchaseInventory.footprint z S k := by
      unfold PurchaseInventory.footprint
      positivity
    apply spillRows_below
    · change A.base v.mesh (.feed b)+PurchaseInventory.footprint z S k+PurchaseInventory.footprint z S k ≤
        A.base v.mesh (.feed b)+A.stride
      omega
    · intro i
      change 0<A.base v.mesh (.feed b)+A.stride
      omega

private theorem shelf_before_tests {n d k₀ q₀ goods : ℕ} (f : Format n d k₀ q₀ goods) :
    f.market.shelf.firstBase ≤ f.testsStart := by
  unfold Format.testsStart Market.flags PurchaseFrozen.Shelf.flagsBase
  omega

private theorem order_of_layout {n d k₀ q₀ goods : ℕ} (f : Format n d k₀ q₀ goods)
    (base selector failed thresholds : ℕ) (failureBase : f.market.failures.base = base+selector)
    (shelfBase : f.market.shelf.firstBase = base+selector+failed+thresholds) :
    base ≤ f.market.failures.base ∧ base ≤ f.market.shelf.firstBase ∧ base ≤ f.testsStart := by
  have first : base ≤ f.market.shelf.firstBase := by rw [shelfBase]; omega
  exact ⟨(Nat.le_add_right base selector).trans failureBase.symm.le, first, first.trans (shelf_before_tests f)⟩

set_option cleanup.letToHave false in
set_option maxHeartbeats 600000 in
theorem posted_attempt_order (a : Attempt) :
    let start := (v.privateArena P z width).base v.mesh (.attempt a)
    let f := v.nativeFormats P z width a
    start ≤ f.market.failures.base ∧ start ≤ f.market.shelf.firstBase ∧ start ≤ f.testsStart := by
  intro base f
  let seed := v.seed P z width
  let sized := v.sized seed width
  let slab := v.slab seed P width
  have failureBase : f.market.failures.base = base + Slab.selectorSpan sized := by cases a <;> rfl
  have shelfBase : f.market.shelf.firstBase = Slab.first slab sized base := by cases a <;> rfl
  exact order_of_layout f base (Slab.selectorSpan sized) (Slab.failureSpan sized)
    (2^(z+slab.thresholdExtra)) failureBase shelfBase

/-- Earlier published rows stay readable during all phases of the later event. -/
theorem event_prefix (e : Event) (x : ℕ) (lower : x<(v.privateArena P z width).base v.mesh e) :
    let C:=v.nativeChart P z width r banks src tab dst owners
    protected C x e ∧ outside C x e := by
  let arena:=v.privateArena P z width
  let f:=v.nativeFormats P z width
  let B:=v.nativeBoards P z width
  exact priced_event_floor_for (N:=S) v.mesh v.finish (v.basePhase width) arena f P.joint.initial width v.keepLimit
    (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase (fun a=>(StripChart.header F B a).fieldTerm)
    (StripChart.id F B P.catalogue) (v.posted_attempt_order P z width) e x lower

/-- Both a frozen repair and an integer reserve feed increase the account by
the signed sum of their own actual width and key words at return. -/
theorem append_paid (e : Event) (m : Memory (wordBits z (2^v.W) copies))
    (live : e∈events v.mesh) :
    let C:=v.nativeChart P z width r banks src tab dst owners
    let _G:=v.privateArena P z width
    let issued:=v.issued P z width r banks src tab dst owners
    let A:=v.billedAccount P z width r banks src tab dst owners
    let indexes:=Succession v.mesh e
    ready C e m →
    (A.read indexes.2 (after C e m)).paid=(A.read indexes.1 m).paid+(issued e).bill width (after C e m) := by
  intro C G issued A indexes run
  have frame (x : ℕ) (before : x<G.base v.mesh e) :=
    (v.event_prefix P z width r banks src tab dst owners e x before).1
  let H:=postedRows v.mesh issued
  have safe : ∀i, let row:=H.word (cursor v.mesh indexes.1) i
      protected C row.width e ∧ protected C row.key e := by
    rw [Succession.at]
    intro i
    apply H.safe C G e i _ frame
    intro t _ j
    exact postedRows_below v.mesh issued G (fun e _=>v.issued_room P z width r banks src tab dst owners e) t
  have h:=H.post A C indexes.1 indexes.2 e m (Succession.next v.mesh e) run safe
  change (A.read indexes.2 (after C e m)).paid=(A.read indexes.1 m).paid+
    (scheduleRows v.mesh issued (cursor v.mesh indexes.1)).bill width (after C e m) at h
  rw [Succession.at,scheduleRows_current v.mesh issued live] at h
  exact h

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
