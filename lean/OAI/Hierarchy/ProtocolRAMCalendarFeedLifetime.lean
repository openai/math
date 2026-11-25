import OAI.Hierarchy.ProtocolRAMPostWriteFloor
import OAI.Hierarchy.ProtocolRAMCalendarPurchaseTailSafe
import OAI.Hierarchy.ProtocolRAMStockStageFrame
import OAI.Hierarchy.ProtocolRAMCalendarTailPositions
import OAI.Hierarchy.ProtocolRAMCalendarFeedLayout
import OAI.Hierarchy.ProtocolRAMCalendarMarketFrame
import OAI.Hierarchy.ProtocolRAMCalendarMount
import OAI.Hierarchy.ProtocolRAMCalendarArchive

namespace OAI
/-! # Protection of earlier reports, prices and purchased reserves across the installed calendar -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ProbeStage ProbeStage.Native PurchaseStage
open scoped Classical
noncomputable section

variable {z d k q goods r edges N w : ℕ}

/-- Common part of the two installed charts: guard, frozen scans, tests,
the emitted pass list, and the final verdict retain every earlier address. -/
private theorem earlier_attempt (c : Mesh) (s : ℝ) (prices : PhasePrice)
    (F : Attempt→Format z d k q goods) (guardAt : Attempt→ℕ)
    (commit : Attempt→Batch q goods → Commit (wordBits z d copies))
    (feeds : Boundary→List CommodityColumn) (a : Attempt) (x : ℕ)
    (stop : x<guardAt a) (fail : x<(F a).market.failures.base) (sampler : x<(F a).market.shelf.firstBase)
    (test : x<(F a).testsStart) (kept : ∀ b,(commit a b).keeps x) :
    let C := chartWith c (fun t=>(F t).board.modeOut) guardAt (fun t=>(F t).atTime c s prices t)
      commit (fun t=>(F t).board) feeds
    protected C x (.attempt a) ∧ outside C x (.attempt a) := by
  let C := chartWith c (fun t=>(F t).board.modeOut) guardAt (fun t=>(F t).atTime c s prices t)
    commit (fun t=>(F t).board) feeds
  let L := C.layout a
  let B := repair C a
  let p := F a
  change x<p.testsStart at test
  have mask : x<p.maskStart := by
    change x<p.testsStart+1+_+_+_
    omega
  have col (i : ℕ) : x<PostLayout.column p.maskStart p.indexBits L.candidates i := by
    exact mask.trans_le ((((Nat.le_add_right p.maskStart (2 ^ p.indexBits)).trans
      (Nat.le_add_right _ L.candidates)).trans (Nat.le_add_right _ 2)).trans
      (Nat.le_add_right _ (i * L.candidates)))
  have price : x<B.keys := mask.trans_le (Nat.le_add_right _ _)
  have tally : x<B.tally := (mask.trans_le (Nat.le_add_right p.maskStart (2^p.indexBits))).trans_le (Nat.le_add_right _ L.candidates)
  have verdict : x<B.verdict := col _
  have scan : ∀ t∈writes L B,x<t.out :=
    writes_after L B x (col _) (col _) (col _) (fun _=>col _) (fun _=>col _) (fun _=>col _) (fun _=>col _) (fun _=>col _)
  have audit : ∀ u∈audits L B,x<u.low ∧ auditOutside x u := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · exact ⟨price,Or.inl price,Or.inl tally⟩
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hu
      exact ⟨scan t ht,Or.inl (scan t ht)⟩
  have fresh : x<(C.frozen a).start :=
    lt_min fail sampler
  have ex : x<B.tests.excess.out := by change x<p.testsStart+1; omega
  have pay : x<B.tests.payload.out := by change x<p.testsStart+1+_+1; omega
  have disc : x<B.tests.discrepancy.out := by change x<p.testsStart+1+_+1+_+1; omega
  exact ⟨⟨stop,Or.inl fresh,ex,pay,disc,mask,fun u hu=>(audit u hu).1,verdict,kept _⟩,
    ⟨Or.inl stop,Or.inl fresh,Or.inl ex,Or.inl pay,Or.inl disc,Or.inl mask,fun u hu=>(audit u hu).2,
      Or.inl verdict,kept _⟩⟩

theorem Format.tests_after_sampler (p : Format z d k q goods) : p.market.shelf.firstBase≤p.testsStart := by
  unfold Format.testsStart Market.flags PurchaseFrozen.Shelf.flagsBase
  omega

private theorem label_after_tests (p : Format z d k q goods) : p.testsStart≤p.labelStart := by
  have mask : p.testsStart≤p.maskStart := by
    change p.testsStart≤p.testsStart+1+_+_+_
    omega
  exact ((((mask.trans (Nat.le_add_right _ (2^p.indexBits))).trans
    (Nat.le_add_right _ p.market.layout.candidates)).trans (Nat.le_add_right _ 2)).trans
    (Nat.le_add_right _ (PostLayout.columnsCount p.checkedBoard * p.market.layout.candidates))).trans
    (Nat.le_add_right _ 1)

/-- A price trial starts its three machine parts at the failure band, the first
sampler pass, and the tests. Their later addresses are inferred from the native
format, including the label source's own freshly archived word range. -/
theorem priced_attempt_floor (c : Mesh) (s : ℝ) (prices : PhasePrice)
    (F : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (a : Attempt) (x : ℕ)
    (fail : x<(F a).market.failures.base) (sampler : x<(F a).market.shelf.firstBase) (test : x<(F a).testsStart) :
    let C := pricedInstalled c s prices F feeds sink idBase role ids
    protected C x (.attempt a) ∧ outside C x (.attempt a) := by
  apply earlier_attempt c s prices F _ _ feeds a x test fail sampler test
  intro b
  apply StockCommit.priced_keeps
  · exact le_rfl
  · left
    change x<(F a).labelStart
    exact test.trans_le (label_after_tests _)

theorem installed_attempt_floor (c : Mesh) (s : ℝ) (prices : PhasePrice)
    (F : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn) (a : Attempt) (x : ℕ)
    (stop : x<(F a).testsStart) (fail : x<(F a).market.failures.base)
    (sampler : x<(F a).market.shelf.firstBase) (test : x<(F a).testsStart) :
    let C := installed c s prices F feeds
    protected C x (.attempt a) ∧ outside C x (.attempt a) := by
  apply earlier_attempt c s prices F _ _ feeds a x stop fail sampler test
  intro b
  apply StockCommit.fresh_keeps
  left
  exact test.trans_le (label_after_tests _)

/-- The installed trial format and the arena shape may be computed separately:
the latter determines the chronological feed bases, and each fitted board determines
its own tested expressions. -/
theorem priced_event_floor_with (c : Mesh) (s : ℝ) (prices : PhasePrice)
    (arena : Arena) (shape F : Attempt→Format z d k q goods) (initial width cap : ℕ) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (order : ∀ a,arena.base c (.attempt a)≤(F a).market.failures.base ∧
      arena.base c (.attempt a)≤(F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤(F a).testsStart)
    (e : Event) (x : ℕ) (prior : x<arena.base c e) :
    let C := pricedInstalled c s prices F (feedColumns (N:=N) c arena shape initial width cap) sink idBase role ids
    protected C x e ∧ outside C x e := by
  cases e with
  | attempt a =>
    exact priced_attempt_floor _ _ _ _ _ _ _ _ _ _ _
      (prior.trans_le (order a).1) (prior.trans_le (order a).2.1) (prior.trans_le (order a).2.2)
  | feed b =>
    let C := pricedInstalled c s prices F (feedColumns (N:=N) c arena shape initial width cap) sink idBase role ids
    have keep := (FeedLayout.atEvent (N:=N) c arena shape initial width cap b).safe_below C b rfl x prior
    exact ⟨keep,fun u hu=>Or.inl (keep u hu)⟩

theorem priced_event_floor_for (c : Mesh) (s : ℝ) (prices : PhasePrice)
    (arena : Arena) (F : Attempt→Format z d k q goods) (initial width cap : ℕ) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (order : ∀ a,arena.base c (.attempt a)≤(F a).market.failures.base ∧
      arena.base c (.attempt a)≤(F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤(F a).testsStart)
    (e : Event) (x : ℕ) (prior : x<arena.base c e) :
    let C := pricedInstalled c s prices F
      (feedColumns (N:=N) c arena F initial width cap) sink idBase role ids
    protected C x e ∧ outside C x e :=
  priced_event_floor_with c s prices arena F F initial width cap sink idBase role ids order e x prior

theorem priced_event_floor (c : Mesh) (s : ℝ) (prices : PhasePrice)
    (arena : Arena) (F : Attempt→Format z d k q goods) (initial width cap : ℕ) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (order : ∀ a,arena.base c (.attempt a)≤(F a).market.failures.base ∧
      arena.base c (.attempt a)≤(F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤(F a).testsStart)
    (e : Event) (x : ℕ) (prior : x<arena.base c e) :
    let C := pricedInstalled c s prices (stockFormats c arena F initial)
      (feedColumns (N:=N) c arena F initial width cap) sink idBase role ids
    protected C x e ∧ outside C x e :=
  priced_event_floor_with c s prices arena F (stockFormats c arena F initial) initial width cap sink idBase role ids order e x prior

/-- The historical word at a reserve feed is the decision actually emitted at
its own purchase attempt; this works on purchases and on every no-buy branch. -/
theorem mode_at_feed (C : Chart w q goods) (arena : Arena) (mem : Memory w) (p a j : ℕ)
    (whole : mounted C (events C.mesh) mem)
    (archive : ArchiveRoom C mem (C.mesh.inject+C.mesh.cool))
    (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps)
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e)
    (slab : C.modeAt (.outer p a)<arena.base C.mesh (.attempt (.outer p a))+arena.stride) :
    (innerState C mem p a j C.mesh.innerFuel (C.modeAt (.outer p a))).val=observedMode C mem p a := by
  have lifetime := purchaseTail_safe C arena p a j C.mesh.innerFuel _ floor slab
  have preserved := purchase_archive C mem p a j C.mesh.innerFuel _ (purchaseTail_mounted whole hp ha hj le_rfl) lifetime
  exact (congrArg Fin.val preserved).trans (archive.outer_word hp ha)

/-- Local version: the archived purchase flag only needs the emitting
native board at this one trial, together with the true intervening writes. -/
theorem mode_at_feed_local (C : Chart w q goods) (arena : Arena) (mem : Memory w) (p a j : ℕ)
    (whole : mounted C (events C.mesh) mem) (wide : 4≤2^w)
    (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps)
    (board : PurchaseStage.Board (C.layout (.outer p a)) (repair C (.outer p a)) w)
    (positive : 0<(C.layout (.outer p a)).candidates)
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e)
    (slab : C.modeAt (.outer p a)<arena.base C.mesh (.attempt (.outer p a))+arena.stride) :
    (innerState C mem p a j C.mesh.innerFuel (C.modeAt (.outer p a))).val=observedMode C mem p a := by
  have keep := purchase_archive C mem p a j C.mesh.innerFuel _
    (purchaseTail_mounted whole hp ha hj le_rfl) (purchaseTail_safe C arena p a j C.mesh.innerFuel _ floor slab)
  have word := observed_mode_word C mem p a ⟨0,positive⟩ (outer_head_ready whole hp ha) board
  have wordFit := (observedMode_lt C mem p a).trans_le wide
  exact (congrArg Fin.val keep).trans (by simpa only [Nat.add_zero,Fin.val_cast_of_lt wordFit] using congrArg Fin.val word)

theorem prepared_prior (C : Chart w q goods) (a : Attempt) (m : Memory w) (x : ℕ)
    (fit : ready C (.attempt a) m) (safe : protected C x (.attempt a)) :
    prepared C a m x=m x := by
  rcases safe with ⟨hg,hf,_⟩
  change (C.frozen a).after ((guard C a).apply m) x=m x
  rw [(C.frozen a).frame _ _ fit.2.1 hf]
  simp [guard,Pass.apply,image,fillSegment,not_le.mpr hg]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
