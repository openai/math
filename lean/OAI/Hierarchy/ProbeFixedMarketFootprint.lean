import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProtocolRAMCalendarStripPrivate
import OAI.Hierarchy.ProtocolRAMCalendarBootFrame

namespace OAI
/-! # Readable CT and sampler cells at the chronological purchase date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart PurchaseStage PurchaseFrozen
open scoped Fin.CommRing Classical
private theorem attempt_upper {z d k q goods r edges : ℕ} (c : Mesh) (finish : ℝ)
    (prices : PhasePrice) (profiles : Attempt → Format z d k q goods)
    (feeds : Boundary → List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt → Expr) (ids : Attempt → Fin goods → Expr) (a : Attempt) (x : ℕ)
    (finishFit : (profiles a).pricedArea.stop ≤ x)
    (fail : (profiles a).market.failures.base + (profiles a).market.failures.rows ≤ (profiles a).testsStart) :
    outside (pricedInstalled c finish prices profiles feeds sink idBase role ids) x (.attempt a) := by
  let circuit := pricedInstalled c finish prices profiles feeds sink idBase role ids
  let p := profiles a
  let L := circuit.layout a
  let T := repair circuit a
  have vend : p.board.verdict+1≤x := (Slab.verdict_before p).trans_le finishFit
  have native (b : Pass) (inList : b∈writes L T) : b.out+b.rows≤p.board.verdict := by
    have shape : PostLayout.place L T p.maskStart p.indexBits=T := by rfl
    rw [←shape] at inList
    obtain ⟨i,hi,o,n⟩ := PostLayout.listed L T _ _ b inList
    rw [o,n]
    change PostLayout.startColumns p.maskStart p.indexBits L.candidates+i*L.candidates+L.candidates≤
      PostLayout.startColumns p.maskStart p.indexBits L.candidates+PostLayout.columnsCount T*L.candidates
    have h := Nat.mul_le_mul_right L.candidates (Nat.succ_le_of_lt hi)
    simpa only [Nat.succ_mul,Nat.add_assoc] using Nat.add_le_add_left h
      (PostLayout.startColumns p.maskStart p.indexBits L.candidates)
  have cols : PostLayout.startColumns p.maskStart p.indexBits p.market.rows≤p.board.verdict :=
    Nat.le_add_right ..
  have bottom : p.testsStart+1≤p.maskStart := by
    unfold Format.maskStart PostLayout.afterTests
    omega
  have maskHi : p.maskStart+p.market.rows≤x := by
    have afterBits := Nat.add_le_add_right (Nat.le_add_right p.maskStart (2^p.indexBits)) p.market.rows
    exact afterBits.trans ((Nat.le_add_right _ 2).trans
      (cols.trans ((Nat.le_succ p.board.verdict).trans vend)))
  have tallyHi : p.maskStart+2^p.indexBits+p.market.rows+2≤x := cols.trans (by omega)
  let tests := (testedBoard p.market.failures p.batch).tests
  let stop := p.testsStart+1
  let limit := stop+(tests.excess.rows+1)+(tests.payload.rows+1)+(tests.discrepancy.rows+1)
  have maskEnd : limit=p.maskStart := rfl
  have ends (n e y d : ℕ) :
      n+e+1≤n+(e+1)+(y+1)+(d+1) ∧
      n+e+1+y+1≤n+(e+1)+(y+1)+(d+1) ∧
      n+e+1+y+1+(d+1)=n+(e+1)+(y+1)+(d+1) := ⟨by omega,by omega,by omega⟩
  obtain ⟨exEnd,pyEnd,dcEnd⟩ := ends stop tests.excess.rows tests.payload.rows tests.discrepancy.rows
  have ex : T.tests.excess.out+T.tests.excess.rows+1≤p.maskStart := calc
    _ = stop+tests.excess.rows+1 := rfl
    _ ≤ limit := exEnd
    _ = _ := maskEnd
  have py : T.tests.payload.out+T.tests.payload.rows+1≤p.maskStart := calc
    _ = stop+tests.excess.rows+1+tests.payload.rows+1 := rfl
    _ ≤ limit := pyEnd
    _ = _ := maskEnd
  have dc : T.tests.discrepancy.out+(T.tests.discrepancy.rows+1)=p.maskStart := calc
    _ = stop+tests.excess.rows+1+tests.payload.rows+1+(tests.discrepancy.rows+1) := rfl
    _ = limit := dcEnd
    _ = _ := maskEnd
  have hi : p.maskStart≤x := by omega
  have bounded : Slab.Bounds circuit a x := by
    refine ⟨(bottom.trans hi),?_,ex.trans hi,py.trans hi,dc.le.trans hi,maskHi,?_,tallyHi,
      fun b hb=>(native b hb).trans (by omega),vend⟩
    · change max (p.market.failures.base+p.market.failures.rows) p.testsStart≤x
      have testHi := (Nat.le_succ p.testsStart).trans (bottom.trans hi)
      exact max_le (fail.trans testHi) testHi
    · change p.maskStart+2^p.indexBits+p.market.rows≤x
      omega
  refine ⟨Or.inr bounded.guard,Or.inr bounded.frozen,Or.inr (by simpa only [Nat.add_assoc] using bounded.excess),
    Or.inr (by simpa only [Nat.add_assoc] using bounded.payload),Or.inr bounded.discrepancy,Or.inr bounded.mask,?_,
    Or.inr bounded.verdict,?_⟩
  · intro u hu
    rcases List.mem_cons.mp hu with rfl|rest
    · exact ⟨Or.inr bounded.keys,Or.inr bounded.tally⟩
    · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp rest
      exact Or.inr (bounded.writes p hp)
  · exact StockCommit.priced_keeps _ _ _ _ x le_rfl (Or.inr finishFit)

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "A" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "fmt" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "W" => wordBits z (2^v.W) copies
local notation "markets" => Whole.markets v.mesh v.finish (v.basePhase width) fmt

set_option cleanup.letToHave false in
set_option maxHeartbeats 800000 in
/-- The original read-only threshold follows the failed-row scratch bank.
The guard follows the flags for every actual candidate. -/
theorem market_regions (a : Attempt) :
    let m:=(fmt a).atTime v.mesh v.finish (v.basePhase width) a
    (A).base v.mesh (.attempt a)≤ m.failures.base ∧
    m.failures.base+m.failures.rows≤Boot.low m ∧ Boot.low m≤ m.shelf.firstBase ∧
    Boot.high m≤ m.flags+m.rows ∧ m.flags+m.rows=(fmt a).testsStart := by
  let seed:=v.seed P z width
  let sized:=v.sized seed width
  let slab:=v.slab seed P width
  have failed : (fmt a).market.failures.base=(A).base v.mesh (.attempt a)+Slab.selectorSpan sized := by
    cases a <;> rfl
  have count : (fmt a).market.failures.rows=Slab.rows sized := by
    simp only [Slab.rows_eq]
    cases a <;> rfl
  have threshold : (fmt a).market.shelf.table.base=
      (A).base v.mesh (.attempt a)+Slab.selectorSpan sized+Slab.failureSpan sized := by
    cases a <;> rfl
  have first : (fmt a).market.shelf.firstBase=Slab.first slab sized ((A).base v.mesh (.attempt a)) := by
    cases a <;> rfl
  change _≤(fmt a).market.failures.base ∧
    (fmt a).market.failures.base+(fmt a).market.failures.rows≤(fmt a).market.shelf.table.base ∧
    (fmt a).market.shelf.table.base≤(fmt a).market.shelf.firstBase ∧
    (fmt a).market.flags≤(fmt a).market.flags+(fmt a).market.rows ∧ _
  have fit : Slab.rows sized≤Slab.failureSpan sized := Slab.row_room sized
  rw [failed,count,threshold,first]
  exact ⟨Nat.le_add_right ..,Nat.add_le_add_left fit _,Nat.le_add_right ..,Nat.le_add_right ..,rfl⟩

/-- All output columns of this calendar event are below the next arena slot.
The bounds depend only on physical column offsets, including the reserve-rebased chart. -/
theorem event_above (e : Event) (x : ℕ) (higher : (A).base v.mesh e+(A).stride≤x) :
    outside C x e := by
  cases e with
  | feed b =>
    let l:=FeedLayout.atEvent («N»:=N) v.mesh A fmt P.joint.initial width v.keepLimit b
    intro p hp
    right
    apply (l.generated_extent C b rfl p hp).trans
    change (A).base v.mesh (.feed b)+PurchaseInventory.footprint z N k+PurchaseInventory.footprint z N k≤x
    have room:=v.feed_room P z width
    omega
  | attempt a =>
    let f:=fmt a
    obtain ⟨_,failed,first,_,_⟩:=v.market_regions P z width a
    have test := Format.tests_after_sampler f
    have failureRoom : f.market.failures.base+f.market.failures.rows ≤ f.testsStart :=
      failed.trans (first.trans test)
    exact attempt_upper v.mesh v.finish (v.basePhase width) fmt
      (feedColumns («N»:=N) v.mesh A fmt P.joint.initial width v.keepLimit)
      (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
      (fun j=>(StripChart.header F B j).fieldTerm) (StripChart.id F B P.catalogue) a x
      ((v.attempt_room P z width a).trans higher) failureRoom

/-- At a real slot the earlier procedures preserve the same CT and preinstalled sampler
cells consumed by this purchase. Both addresses of the current guard and failures are fresh. -/
theorem market_frames (a : Attempt) (prior : List Event)
    (heap : heapEnd z (2^v.W) copies≤(A).first)
    (earlier : ∀e∈prior,position v.mesh e<position v.mesh (.attempt a)) :
    let m:=(fmt a).atTime v.mesh v.finish (v.basePhase width) a
    (∀x,Boot.reads m x→∀e∈prior,outside C x e) ∧
    (∀x,Boot.reads m x→x≠(C).stopAt a) ∧
    (∀x,Boot.reads m x→apart x m.failures.base m.failures.rows) := by
  let m:=(fmt a).atTime v.mesh v.finish (v.basePhase width) a
  obtain ⟨before,failed,table,_,guard⟩:=v.market_regions P z width a
  have low (e : Event) : heapEnd z (2^v.W) copies≤(A).base v.mesh e := heap.trans (Nat.le_add_right ..)
  have g0:((C).stopAt a)=m.flags+m.rows:=guard.symm
  have eg := v.stock_order P z width a
  have belowGuard : (A).base v.mesh (.attempt a)≤(C).stopAt a:=eg.2.2
  refine ⟨?_,?_,?_⟩
  · intro x hx e member
    rcases hx with ct|⟨lo,hi⟩
    · exact (v.event_prefix P z width r banks src tab dst owners e x (ct.trans_le (low e))).2
    · exact v.event_above P z width r banks src tab dst owners e x
        (((A).apart v.mesh (earlier e member)).trans (before.trans ((Nat.le_add_right ..).trans (failed.trans lo))))
  · intro x hx
    rcases hx with ct|⟨lo,hi⟩
    · exact (ct.trans_le ((low _).trans belowGuard)).ne
    · rw [g0]
      exact (hi.trans_le (Nat.le_add_right ..)).ne
  · intro x hx
    rcases hx with ct|⟨lo,hi⟩
    · exact Or.inl (ct.trans_le ((low _).trans before))
    · exact Or.inr (failed.trans lo)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
