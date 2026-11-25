import OAI.Hierarchy.ProtocolRAMCalendarMarketFrame
import OAI.Hierarchy.ProtocolRAMCalendarPriced

namespace OAI
/-! # The address above all post-snapshot tests, inspection and receipt columns -/

namespace Hierarchy.ProtocolRAM.Calendar
open ProbeStage ProbeStage.Native PurchaseStage
open scoped Classical
variable {z d k q goods r edges w : ℕ}

def PostOutside (L : Dispatch) (B : Repair q goods) (x : ℕ) : Prop :=
  apart x B.tests.excess.out (B.tests.excess.rows+1) ∧
  apart x B.tests.payload.out (B.tests.payload.rows+1) ∧
  apart x B.tests.discrepancy.out (B.tests.discrepancy.rows+1) ∧
  apart x B.repairBits.base L.candidates ∧ ∀ s∈audits L B, auditOutside x s

/-- The six noncolumn spans used by the preliminary tests and the inspection. -/
def PostEnds (L : Dispatch) (B : Repair q goods) : Prop :=
  B.tests.excess.out + (B.tests.excess.rows+1) ≤ B.verdict ∧
  B.tests.payload.out + (B.tests.payload.rows+1) ≤ B.verdict ∧
  B.tests.discrepancy.out + (B.tests.discrepancy.rows+1) ≤ B.verdict ∧
  B.repairBits.base+L.candidates ≤ B.verdict ∧
  B.keys+L.candidates ≤ B.verdict ∧ B.tally+2 ≤ B.verdict

theorem post_outside_of_verdict (L : Dispatch) (B : Repair q goods)
    (ends : PostEnds L B) (written : ∀ p ∈ writes L B, p.out+p.rows≤B.verdict)
    (x : ℕ) (last : B.verdict<x) : PostOutside L B x := by
  rcases ends with ⟨excess,payload,disc,mask,keys,tally⟩
  refine ⟨.inr (excess.trans last.le),.inr (payload.trans last.le),.inr (disc.trans last.le),
    .inr (mask.trans last.le),?_⟩
  intro s hs
  rcases List.mem_cons.mp hs with rfl | h
  · exact ⟨.inr (keys.trans last.le),.inr (tally.trans last.le)⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
    exact .inr ((written p hp).trans last.le)

/-- The placed tests finish exactly where the repair mask begins. Inspection follows
the mask, and all receipt columns follow its two tally bins. -/
theorem Format.post_ends (f : Format z d k q goods) : PostEnds f.market.layout f.board := by
  let t := (testedBoard f.market.failures f.batch).tests
  let n := f.market.layout.candidates
  let endRows := PostLayout.columnsCount f.checkedBoard*n
  have test := PostLayout.tests_separate t f.testsStart
  let s := PostLayout.placeTests t f.testsStart
  have e : s.excess.out+s.excess.rows<s.payload.out := test.2.1
  have p : s.payload.out+s.payload.rows<s.discrepancy.out := test.2.2.1
  have d : s.discrepancy.out+s.discrepancy.rows+1=f.maskStart := test.2.2.2
  have total : f.board.verdict=f.maskStart+2^f.indexBits+n+2+endRows := rfl
  change s.excess.out+(s.excess.rows+1)≤f.board.verdict ∧
    s.payload.out+(s.payload.rows+1)≤f.board.verdict ∧
    s.discrepancy.out+(s.discrepancy.rows+1)≤f.board.verdict ∧
    f.maskStart+n≤f.board.verdict ∧ f.maskStart+2^f.indexBits+n≤f.board.verdict ∧
    f.maskStart+2^f.indexBits+n+2≤f.board.verdict
  have tally_le : f.maskStart+2^f.indexBits+n+2 ≤ f.board.verdict :=
    (Nat.le_add_right _ endRows).trans_eq total.symm
  have keys_le : f.maskStart+2^f.indexBits+n ≤ f.board.verdict :=
    (Nat.le_add_right _ 2).trans tally_le
  have mask_end_le : f.maskStart+n ≤ f.board.verdict :=
    (Nat.add_le_add_right (Nat.le_add_right f.maskStart (2^f.indexBits)) n).trans keys_le
  have mask_le : f.maskStart ≤ f.board.verdict := (Nat.le_add_right _ n).trans mask_end_le
  have discrepancy_le : s.discrepancy.out + (s.discrepancy.rows+1) ≤ f.board.verdict :=
    d.le.trans mask_le
  have payload_le : s.payload.out + (s.payload.rows+1) ≤ f.board.verdict :=
    (Nat.succ_le_of_lt p).trans ((Nat.le_add_right _ _).trans discrepancy_le)
  have excess_le : s.excess.out + (s.excess.rows+1) ≤ f.board.verdict :=
    (Nat.succ_le_of_lt e).trans ((Nat.le_add_right _ _).trans payload_le)
  exact ⟨excess_le,payload_le,discrepancy_le,mask_end_le,keys_le,tally_le⟩

theorem format_post_outside (f : Format z d k q goods) (x : ℕ) (last : f.board.verdict<x) :
    PostOutside f.market.layout f.board x := by
  apply post_outside_of_verdict _ _ f.post_ends _ x last
  intro p hp
  obtain ⟨i,hi,base,rows⟩ := PostLayout.listed f.market.layout f.checkedBoard f.maskStart f.indexBits p hp
  rw [base,rows]
  have le := Nat.mul_le_mul_right f.market.layout.candidates (Nat.succ_le_of_lt hi)
  simp only [Nat.succ_mul] at le
  change PostLayout.startColumns f.maskStart f.indexBits f.market.layout.candidates +
    i*f.market.layout.candidates + f.market.layout.candidates ≤
    PostLayout.startColumns f.maskStart f.indexBits f.market.layout.candidates +
    PostLayout.columnsCount f.checkedBoard*f.market.layout.candidates
  omega

/-- The actual priced chart reuses these addresses when it substitutes the runtime
mode and stop-test expressions. -/
theorem priced_post_outside (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (a : Attempt)
    (legal : let C := pricedInstalled c finish prices format feeds sink idBase role ids
      Board (C.layout a) (repair C a) (wordBits z d copies))
    (x : ℕ) (last : (format a).board.verdict<x) :
    let C := pricedInstalled c finish prices format feeds sink idBase role ids
    PostOutside (C.layout a) (repair C a) x := by
  let C := pricedInstalled c finish prices format feeds sink idBase role ids
  apply post_outside_of_verdict (C.layout a) (repair C a) _ legal.flagAfter x last
  exact (format a).post_ends

private theorem placed_flag_after (L : Dispatch) (B : Repair q goods) (first bits : ℕ)
    (placed : PostLayout.place L B first bits=B) (p : Pass) (hit : p∈writes L B) :
    p.out+p.rows≤B.verdict := by
  have hit' : p∈writes L (PostLayout.place L B first bits) := placed.symm ▸ hit
  obtain ⟨i,hi,addr,rows⟩ := PostLayout.listed L B first bits p hit'
  rw [addr,rows,←congrArg (fun C : Repair q goods => C.verdict) placed]
  have le := Nat.mul_le_mul_right L.candidates (Nat.succ_le_of_lt hi)
  simp only [Nat.succ_mul] at le
  change PostLayout.startColumns first bits L.candidates+i*L.candidates+L.candidates ≤
    PostLayout.startColumns first bits L.candidates+PostLayout.columnsCount B*L.candidates
  omega

theorem priced_post_outside_layout (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (a : Attempt)
    (x : ℕ) (last : (format a).board.verdict<x) :
    let C := pricedInstalled c finish prices format feeds sink idBase role ids
    PostOutside (C.layout a) (repair C a) x := by
  let C := pricedInstalled c finish prices format feeds sink idBase role ids
  let L := C.layout a
  let B := repair C a
  let f := format a
  have fixed : PostLayout.place L B f.maskStart f.indexBits=B := rfl
  exact post_outside_of_verdict L B f.post_ends (placed_flag_after L B _ _ fixed) x last

/-- Entire upper frame of an installed priced attempt, including the guard,
frozen market, mark and score workspaces, and priced commodity commit. -/
theorem priced_attempt_outside_ready (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (a : Attempt)
    (m : PurchaseFrozen.Shelf.Mem z d)
    (ok : ready (pricedInstalled c finish prices format feeds sink idBase role ids) (.attempt a) m)
    (x : ℕ) (afterEnd : (format a).pricedArea.stop≤x) :
    outside (pricedInstalled c finish prices format feeds sink idBase role ids) x (.attempt a) := by
  let C := pricedInstalled c finish prices format feeds sink idBase role ids
  let f := format a
  let v := f.atTime c finish prices a
  have rv : v.ready ((guard C a).apply m) := ok.2.1
  have first := rv.2.1
  have flags : v.shelf.firstBase≤v.flags := by unfold Market.flags PurchaseFrozen.Shelf.flagsBase; omega
  have stopMask : f.testsStart+1≤f.maskStart := by unfold Format.maskStart PostLayout.afterTests; omega
  have maskEnd := f.post_ends.2.2.2.1
  change f.maskStart+f.market.layout.candidates ≤ f.board.verdict at maskEnd
  have last : f.board.verdict<x := by
    have before : f.board.verdict < f.pricedArea.stop := by
      simp only [Format.pricedArea,Format.area,Format.labelStart,StockCommit.Area.stop,StockCommit.Area.output,
        StockCommit.Area.excess,StockCommit.Area.clip,StockCommit.Area.src,StockCommit.Area.broadcast,
        StockCommit.Area.direct]
      omega
    exact before.trans_le afterEnd
  have stopBefore : f.testsStart+1≤x := by omega
  obtain ⟨excess,payload,disc,mask,audit⟩ := priced_post_outside_layout c finish prices format feeds sink idBase role ids a x last
  refine ⟨.inr stopBefore,.inr ?_,excess,payload,disc,mask,audit,.inr (Nat.succ_le_of_lt last),?_⟩
  · change max (v.failures.base+v.failures.rows) (v.flags+v.rows) ≤ x
    change v.flags+v.rows+1≤x at stopBefore
    exact max_le (by omega) (by omega)
  · exact StockCommit.priced_keeps _ _ _ _ x le_rfl (.inr afterEnd)

/-- Entire upper frame of an installed priced attempt, including the guard,
frozen market, mark and score workspaces, and priced commodity commit. -/
theorem priced_attempt_outside (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (a : Attempt)
    (m : PurchaseFrozen.Shelf.Mem z d)
    (ok : ready (pricedInstalled c finish prices format feeds sink idBase role ids) (.attempt a) m)
    (_legal : let C := pricedInstalled c finish prices format feeds sink idBase role ids
      Board (C.layout a) (repair C a) (wordBits z d copies))
    (x : ℕ) (afterEnd : (format a).pricedArea.stop≤x) :
    outside (pricedInstalled c finish prices format feeds sink idBase role ids) x (.attempt a) :=
  priced_attempt_outside_ready c finish prices format feeds sink idBase role ids a m ok x afterEnd

end Hierarchy.ProtocolRAM.Calendar

end OAI
