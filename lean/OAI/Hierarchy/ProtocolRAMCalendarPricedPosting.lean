import OAI.Hierarchy.ProtocolRAMCalendarEventPrices
import OAI.Hierarchy.ProtocolRAMReportedChargeKeys

namespace OAI
/-! # True per-event financial reports on the installed, stamped and seeded calendar -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram PurchaseStage
open scoped BigOperators Classical
noncomputable section
variable {w q d paths : ℕ} {I : Type*}

/-- Port labels from the actual scheduled event specialize the count-only prefix
identity. Earlier immutable charge rows are paid exactly once. -/
theorem posted_event (C : Chart w q d) (e : Event) (initial : Memory w) (M : AccountColumns I)
    (issued : Event→WordRows) {J : Type*} [Fintype J] (rows : J→ChargeWord)
    (kind : issued e=WordRows.ofPorts rows) (live : e∈events C.mesh) (step : ready C e initial)
    (arena : Arena) (fits : ∀t<position C.mesh e,∀r : Fin ((postedRows C.mesh issued).count t),
      ((postedRows C.mesh issued).emit t r).width<arena.first+(t+1)*arena.stride ∧
      ((postedRows C.mesh issued).emit t r).key<arena.first+(t+1)*arena.stride)
    (prior : ∀x,x<arena.base C.mesh e→protected C x e) :
    let A := (postedRows C.mesh issued).account C.mesh M
    let a := Succession C.mesh e
    let out := after C e initial
    (A.read a.2 out).paid=(A.read a.1 initial).paid+
      ∑ i,(rows i).value A.payloadWidth out := by
  intro A a out
  let P := postedRows C.mesh issued
  have pos : cursor C.mesh a.1=position C.mesh e := Succession.at C.mesh e
  have bound (i : Fin (P.size (cursor C.mesh a.1))) :
      protected C (P.word (cursor C.mesh a.1) i).width e ∧ protected C (P.word (cursor C.mesh a.1) i).key e := by
    rw [← P.word_cast pos i]
    exact P.safe C arena e (Fin.cast (congrArg P.size pos) i) fits prior
  have pay := P.post M C a.1 a.2 e initial (Succession.next C.mesh e) step bound
  apply pay.trans
  apply congrArg ((A.read a.1 initial).paid+·)
  rw [pos]
  let K := rowsEquiv C.mesh issued live rows kind
  rw [←K.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowsEquiv_word]

/-- Exact recorded bill of the installed `pricedSegment`, after its live length
stamp pass and its native commodity-seeding preamble. The old account index
is the literal cursor of this event. No probability or pricing hypothesis is
used in the signed increment. -/
theorem priced_attempt (C : Chart w q d) (x : Attempt) (initial : Memory w) (M : AccountColumns I)
    (issued : Event→WordRows) (area : StockCommit.Area) (s : StockCommit.Sources) (g : StockCommit.LabelSource)
    (b : Batch q d) (flags copies : ℕ) (positive : 0<M.payloadWidth)
    (keys : CashKeys area.occurrences area.rows area.goods paths)
    (link : Fin area.occurrences→ℕ→ℝ) (tree : Fin area.rows→ℕ→ℝ)
    (core : Fin area.goods→ℕ→ℝ) (fee : Fin paths→ℕ→ℝ)
    (current : issued (.attempt x)=WordRows.ofPorts
      ((StockCommit.fresh area s).eventWords flags M.payloadWidth copies keys link tree core fee))
    (live : Event.attempt x∈events C.mesh) (step : ready C (.attempt x) initial)
    (installed : C.commit x=StockCommit.pricedSegment area s g w b)
    (board : (StockCommit.fresh area s).EventBoard w)
    (arena : Arena) (fits : ∀t<position C.mesh (.attempt x),∀r : Fin ((postedRows C.mesh issued).count t),
      ((postedRows C.mesh issued).emit t r).width<arena.first+(t+1)*arena.stride ∧
      ((postedRows C.mesh issued).emit t r).key<arena.first+(t+1)*arena.stride)
    (prior : ∀i,i<arena.base C.mesh (.attempt x)→protected C i (.attempt x)) :
    let a := Succession C.mesh (.attempt x)
    let A := (postedRows C.mesh issued).account C.mesh M
    let out := after C (.attempt x) initial
    let z := StockCommit.stageInput area s g (postOutput (C.layout x) (repair C x) (prepared C x initial))
    let f := StockCommit.fresh area s
    (A.read a.2 out).paid=(A.read a.1 initial).paid+
      (linkBill (goods:=area.goods) f.columns f.plan.bank z A.payloadWidth (fun i=>link i (out (keys.link i)).val)+
        (∑j,(copies:ℝ)*(tree j (out (keys.broadcast j)).val*(out (area.broadcast+j.val)).val))/A.payloadWidth+
        (∑i,((out (area.output+area.goods+area.goods+i.val)).val:ℝ)/A.payloadWidth*core i (out (keys.core i)).val)+
        ∑j,(out (flags+j.val)).val*fee j (out (keys.buy j)).val) := by
  intro a A out z f
  have bill := posted_event C (.attempt x) initial M issued _ current live step arena fits prior
  have mounted : (C.commit x).ready (postOutput (C.layout x) (repair C x) (prepared C x initial)) := by
    rcases step with ⟨_,_,_,_,_,_,_,_,_,_,v,_,_⟩
    exact v
  rw [installed] at mounted
  have cash := f.event_receipt b z flags M.payloadWidth copies positive mounted.2.2 board keys link tree core fee
  have finalOutput : out=(f.native w area.rows b).after z := by
    change (C.commit x).after _=_
    rw [installed]
    rfl
  apply bill.trans
  apply congrArg ((A.read a.1 initial).paid+·)
  change (∑ i, (f.eventWords flags M.payloadWidth copies keys link tree core fee i).value M.payloadWidth out) = _
  rw [finalOutput]
  exact cash

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
