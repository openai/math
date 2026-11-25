import OAI.Hierarchy.ProbeInstalledPurchaseWords
import OAI.Hierarchy.ProbeStripQuoteStock
import OAI.Hierarchy.ProtocolRAMCalendarLiveAccounts
import OAI.Hierarchy.ProtocolRAMCalendarScalarHistory

namespace OAI
/-! # Input-derived chronological quote words at a paid reserve correction -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage Native GlobalTests StripDirectory
open scoped BigOperators Classical Fin.CommRing
variable {w z N k q goods : ℕ}

/-- The two earlier score scans write only in the current attempt's area.
Protected scalar ROM, retained bits and the bought archive are read intact
when discrepancy is measured. -/
theorem replay_prior (C : Chart w q goods) (boot : Memory w) (p h j b x : ℕ)
    (step : ready C (.attempt (.inner p h j b)) (innerState C boot p h j b))
    (keep : protected C x (.attempt (.inner p h j b))) :
    replayScoreMemory C boot p h j b x=innerState C boot p h j b x := by
  let u:=Attempt.inner p h j b
  let B:=repair C u
  change B.tests.payload.after (B.tests.excess.after (prepared C u (innerState C boot p h j b))) x=_
  rw [B.tests.payload.frame _ _ keep.2.2.2.1,B.tests.excess.frame _ _ keep.2.2.1]
  exact prepared_prior C u _ x step keep

/-- The true integer stock of each global commodity in the two score lookup
passes. The previous event determines the stock address, even after a repair
or spill. Only the currently read stock *block* is framed through this scan. -/
theorem replay_stock (A : AccountColumns (GlobalTests.Goods z N k)) (C : Chart w q goods)
    (boot : Memory w) (l : GlobalTests.Layout) (stocks : Bank) (s : PhasePrice) (p h j b : ℕ)
    (whole : mounted C (events C.mesh) boot) (hp : p< C.mesh.inject+C.mesh.cool) (hh : h< C.mesh.outerFuel)
    (hj : j< C.mesh.reserveSteps) (hb : b< C.mesh.innerFuel)
    (start : GlobalTests.Resident l z N k s boot)
    (rom : ∀e x,l.base≤ x→x< GlobalTests.stop l z N k→protected C x e)
    (stockAt : ∀i,A.stockAt (.inner p h j b) i=stocks.base+PurchaseInventory.slot i)
    (active : ∀i : Fin (rows z N k),protected C (stocks.base+i.val) (.attempt (.inner p h j b)))
    (size : rows z N k<2^w) (rowBits : rows z N k≤2^l.indexBits) (bankCap : rows z N k≤ stocks.size)
    (digits : span l N k<2^w) (valueCap : span l N k≤2^l.indexBits)
    (bounded : ∀i,(A.inner C boot p h j b).bits i< l.stride)
    (limit : unitBound l N k s<2^w)
    (positive : 0< s.a) (bonus : ∀i< kinds N k,0≤ s.bonus i) (M : 0≤ s.M)
    (time : 0< s.time) (cap : ∀i< kinds N k,0≤ s.cap i) :
    ReadStock A (A.inner C boot p h j b) l stocks s (replayScoreMemory C boot p h j b) := by
  let E:=PurchaseInventory.slotEquiv z N k
  have step:=inner_head_ready whole hp hh hj hb
  have table : GlobalTests.Resident l z N k s (replayScoreMemory C boot p h j b) := by
    apply start.transport
    intro x lo hi
    rw [replay_prior C boot p h j b x step (rom _ x lo hi),FeedLayout.inner_as_run]
    exact run_frame C _ _ x (beforeInner_mounted C boot p h j b whole hp hh hj hb.le)
      (fun ev _=>rom ev x lo hi)
  have bits (i : Fin (rows z N k)) :
      (replayScoreMemory C boot p h j b (stocks.base+i.val)).val=(A.inner C boot p h j b).bits (E.symm i) := by
    rw [replay_prior C boot p h j b _ step (active i)]
    change _=((innerState C boot p h j b) (A.stockAt (.inner p h j b) (E.symm i))).val
    rw [stockAt]
    have key:=congrArg Fin.val (E.apply_symm_apply i)
    change PurchaseInventory.slot (E.symm i)=i.val at key
    rw [key]
  refine ⟨table,size,rowBits,bankCap,digits,valueCap,fun i=>by rw [bits i];exact bounded _,?_,bits⟩
  intro pay i
  exact (valueWord_le l s pay (kind i) _ positive (bonus _ (kind i).isLt) M time (cap _ (kind i).isLt)).trans_lt limit

/-- The rounded price ROM is the actual finite list of calendar deadlines,
mounted once at startup. The caller supplies the score/cap receipt on precisely
the same current integer stock, as produced by `replay_stock`. -/
theorem replay_quote_cells (A : AccountColumns (GlobalTests.Goods z N k)) (C : Chart w q goods)
    (boot : Memory w) (l : GlobalTests.Layout) (stocks : Bank) (finish : ℝ) (prices : PhasePrice)
    (base p h j b : ℕ) (hp : p≤ C.mesh.inject+C.mesh.cool) (hj : j≤ C.mesh.reserveSteps) :
    let u:=Attempt.inner p h j b
    let s:=deadline C.mesh finish prices u
    let m:=replayScoreMemory C boot p h j b
    let t:=DeadlineROM.table C.mesh finish prices base (kinds N k) l.stride
    let word:=t.bank (DeadlineROM.index C.mesh u)
    ReadStock A (A.inner C boot p h j b) l stocks s m → t.Resident (innerState C boot p h j b) →
    ready C (.attempt u) (innerState C boot p h j b) →
    (∀x,t.base≤ x→x< t.stop→protected C x (.attempt u)) →
    QuoteCells s m word (offsets l) stocks PurchaseInventory.slot PurchaseInventory.lane
      (A.inner C boot p h j b).bits l.stride := by
  intro u s m t word R memory step protectedAt
  have held : t.Resident m := memory.frame (fun x lo hi=>replay_prior C boot p h j b x step (protectedAt x lo hi))
  exact QuoteCells.ofStock R word (DeadlineROM.read_inner C.mesh finish prices base (kinds N k) l.stride p h j b m held hp hj)

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
