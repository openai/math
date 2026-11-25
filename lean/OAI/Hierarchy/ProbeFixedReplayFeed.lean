import OAI.Hierarchy.ProbeFixedFeedWordRoom
import OAI.Hierarchy.ProbeFixedFeedBill
import OAI.Hierarchy.ProtocolRAMCalendarHalfBoot
import OAI.Hierarchy.ProtocolRAMCalendarFeedStock
import OAI.Hierarchy.ProbeFixedNativeStockRun

namespace OAI
/-! # Actual reserve-slice word, spill, charge and terminal state of a successful purchase -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart
open ThreeFlat.RAM
open StockCommit PurchaseStage
open scoped Fin.CommRing Classical BigOperators
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "stride" => v.keepLimit*width+1
local notation "table" => sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps stride
local notation "Good" => FeedLayout.Good z N k

theorem replay_terminal (mem : Memory W) (u a : ℕ) :
    (A).inner C mem u a v.mesh.reserveSteps 0=(A).trial C mem u (a+1) :=
  nativeAccounts_outer_next C G f P.joint.initial width (v.issued P z width r banks src tab dst owners)
    _ _ _ _ _ mem u a

section ReplayFeed
set_option maxRecDepth 8192

variable (mem fixture : Memory (wordBits z (2^v.W) copies))
  (stock : StockBound.Run (v.nativeChart P z width r banks src tab dst owners) (v.stockBanks P z width) mem z (CoreBoard.Stages z (2^v.W)) k (v.keepLimit*width))
  (initialRoom : (sliceROM (P.joint.initial+PurchaseInventory.footprint z (CoreBoard.Stages z (2^v.W)) k) v.mesh.reserveSteps (v.keepLimit*width+1)).base+(sliceROM (P.joint.initial+PurchaseInventory.footprint z (CoreBoard.Stages z (2^v.W)) k) v.mesh.reserveSteps (v.keepLimit*width+1)).size≤(v.privateArena P z width).first) (addressRoom : (v.privateArena P z width).endAddress v.mesh<2^(wordBits z (2^v.W) copies))
  (headroom : 2*(v.keepLimit*width)<2^(wordBits z (2^v.W) copies))
  (sliceData : ∀x,(sliceROM (P.joint.initial+PurchaseInventory.footprint z (CoreBoard.Stages z (2^v.W)) k) v.mesh.reserveSteps (v.keepLimit*width+1)).base≤x→x<(sliceROM (P.joint.initial+PurchaseInventory.footprint z (CoreBoard.Stages z (2^v.W)) k) v.mesh.reserveSteps (v.keepLimit*width+1)).base+v.mesh.reserveSteps*(v.keepLimit*width+1)→
    mem x=feedAdvice (sliceROM (P.joint.initial+PurchaseInventory.footprint z (CoreBoard.Stages z (2^v.W)) k) v.mesh.reserveSteps (v.keepLimit*width+1)) v.mesh.reserveSteps (v.keepLimit*width+1) fixture x)
  (u a : ℕ) (hu : u<v.mesh.inject+v.mesh.cool) (ha : a<v.mesh.outerFuel)
  (layout : StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) (.outer u a) (v.nativeFormats P z width (.outer u a)).pricedArea (v.nativeFormats P z width (.outer u a)).stockSource
    (v.stamp P z width r banks src tab dst owners (.outer u a))
    v.keepLimit width ((v.privateArena P z width).base v.mesh (.attempt (.outer u a))))
  (bought : observedMode (v.nativeChart P z width r banks src tab dst owners) mem u a=3)
  (saved : ∀i : (FeedLayout.Good z (CoreBoard.Stages z (2^v.W)) k),PurchaseInventory.stock ((v.nativeFormats P z width (.outer u a)).pricedArea.output+(v.nativeFormats P z width (.outer u a)).pricedArea.goods)
    (reserveState (v.nativeChart P z width r banks src tab dst owners) mem u a 0) i=((v.billedAccount P z width r banks src tab dst owners).trial (v.nativeChart P z width r banks src tab dst owners) mem u a).bits i-((v.billedAccount P z width r banks src tab dst owners).trial (v.nativeChart P z width r banks src tab dst owners) mem u a).bits i/2)

include stock initialRoom addressRoom headroom sliceData hu ha layout bought saved in
theorem replay_feed_words (j : ℕ) (hj : j<v.mesh.reserveSteps) (i : Good) :
    let L:=FeedLayout.atEvent («N»:=N) v.mesh G f P.joint.initial width v.keepLimit (.inner u a j)
    let req : Good → ℕ := (A).bank.replayFeed v.mesh.reserveSteps j ((A).trial C mem u a) ((A).inner C mem u a j v.mesh.innerFuel)
    ((A).inner C mem u a (j+1) 0).bits i=min (req i) (v.keepLimit*width) ∧
      (reserveState C mem u a (j+1) (L.overflow+PurchaseInventory.slot i)).val=spillBits v.keepLimit width req i := by
  intro L req
  let e := Event.feed (.inner u a j)
  let parent := Attempt.outer u a
  have live : e∈events v.mesh := innerFeed_occurs v.mesh hu ha hj
  obtain ⟨_,atFeed⟩ := inner_feed_slot C mem u a j hu ha hj stock.mounted_all
  obtain ⟨_,atOuter⟩ := outer_slot C mem u a hu ha stock.mounted_all
  obtain ⟨early,space⟩ := v.stock_feed P z width r banks src tab dst owners (.inner u a j) live initialRoom addressRoom
  have cap : v.keepLimit*width<2^W := by omega
  have rowRoom : 2^z≤2^W := Nat.pow_le_pow_right (by decide) (by unfold wordBits;omega)
  have old : ((A).trial C mem u a).bits i≤v.keepLimit*width := (stock.slot atOuter).1 i
  have prev := stockAt_inner_end v.mesh G f P.joint.initial width v.keepLimit u a j i
  have next := stockAt_inner_next v.mesh G f P.joint.initial width v.keepLimit u a j i hu ha hj
  have prior : ((A).inner C mem u a j v.mesh.innerFuel).bits i≤v.keepLimit*width := by
    change ((innerState C mem u a j v.mesh.innerFuel) ((A).stockAt (.inner u a j v.mesh.innerFuel) i)).val≤_
    rw [show (A).stockAt (.inner u a j v.mesh.innerFuel) i=L.active+PurchaseInventory.slot i from prev]
    exact (stock.slot atFeed).1 i
  have want : req i<2^W := by
    change ((A).inner C mem u a j v.mesh.innerFuel).bits i+
      slice v.mesh.reserveSteps (((A).trial C mem u a).bits i-((A).trial C mem u a).bits i/2) j < _
    have sl:=FeedLayout.slice_le_total (((A).trial C mem u a).bits i-((A).trial C mem u a).bits i/2) hj
    omega
  have floor (ev : Event) (x : ℕ) (lo : x<(G).base v.mesh ev) :=
    (v.event_prefix P z width r banks src tab dst owners ev x lo).1
  have mode : reserveState C mem u a 0 ((C).modeAt parent)=3 := by
    have observed := observed_mode_word C mem u a ⟨0,layout.positive⟩ atOuter.currentReady layout.board
    simpa only [Nat.add_zero,bought,Nat.cast_ofNat] using observed
  have tag : (C).modeAt parent<(G).base v.mesh (.attempt parent)+(G).stride := v.stock_mode_room P z width parent
  have idx : PurchaseInventory.slot i<PurchaseInventory.footprint z N k := PurchaseInventory.slot_lt i
  have store := v.stock_post_span P z width parent
  have pass0 := purchaseTail_safe C G u a j v.mesh.innerFuel ((C).modeAt parent) floor tag
  have srcBound : L.saved+PurchaseInventory.slot i<(G).base v.mesh (.attempt parent)+(G).stride := by
    change (f parent).pricedArea.output+(f parent).pricedArea.goods+PurchaseInventory.slot i<_
    omega
  have pass1 := purchaseTail_safe C G u a j v.mesh.innerFuel (L.saved+PurchaseInventory.slot i) floor srcBound
  have tableSize := sliceROM_size (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps stride
  have tableFloor : (table).base+v.mesh.reserveSteps*stride≤(G).first :=
    (Nat.add_le_add_left tableSize _).trans initialRoom
  have termBound : v.mesh.reserveSteps*stride<2^W :=
    (Nat.le_add_left ..).trans_lt (tableFloor.trans_lt ((Nat.le_add_right (G).first _).trans_lt addressRoom))
  have rom := Boot.slice_before_feed C G mem fixture table stride u a j stock.mounted_all hu ha hj
    tableFloor floor sliceData
  exact L.retained A C mem fixture u a j rfl early space cap rowRoom i hj rfl prev next mode (saved i)
    (purchaseTail_mounted stock.mounted_all hu ha hj le_rfl) (fun ev hev=>⟨pass0 ev hev,pass1 ev hev⟩)
    (by change _<v.keepLimit*width+1;omega) tableSize termBound rom want

include stock initialRoom addressRoom headroom sliceData hu ha layout bought saved in
theorem replay_feed_paid (j : ℕ) (hj : j<v.mesh.reserveSteps) :
    let before : Inventory Good := (A).inner C mem u a j v.mesh.innerFuel
    let finish : Inventory Good := (A).inner C mem u a (j+1) 0
    let req : Good → ℕ := (A).bank.replayFeed v.mesh.reserveSteps j ((A).trial C mem u a) before
    finish.paid=before.paid+pairing (bitStock width (spillBits v.keepLimit width req)) (A).box := by
  intro before finish req
  let L:=FeedLayout.atEvent («N»:=N) v.mesh G f P.joint.initial width v.keepLimit (.inner u a j)
  obtain ⟨_,cut⟩:=inner_feed_slot C mem u a j hu ha hj stock.mounted_all
  have live : Event.feed (.inner u a j)∈events v.mesh := innerFeed_occurs v.mesh hu ha hj
  have receipt : finish.paid=before.paid+∑i : Good,
      ((reserveState C mem u a (j+1) (L.overflow+PurchaseInventory.slot i)).val:ℝ)*(A).box i/width := by
    dsimp only [finish,before,AccountColumns.inner,inner_zero]
    rw [reserve_succ]
    exact v.feed_bill P z width r banks src tab dst owners (.inner u a j) _ live cut.currentReady
  rw [receipt]
  apply congrArg (before.paid+·)
  change (∑i : Good,((reserveState C mem u a (j+1) (L.overflow+PurchaseInventory.slot i)).val:ℝ)*(A).box i/width)=
    ∑i,(bitStock width (spillBits v.keepLimit width req) i)*(A).box i
  apply Finset.sum_congr rfl
  intro i _
  rw [(v.replay_feed_words P z width r banks src tab dst owners mem fixture stock initialRoom addressRoom
    headroom sliceData u a hu ha layout bought saved j hj i).2]
  unfold bitStock
  ring

end ReplayFeed

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
