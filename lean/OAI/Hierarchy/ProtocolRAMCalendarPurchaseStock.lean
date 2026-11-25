import OAI.Hierarchy.ProtocolRAMCalendarFeedPurchase
import OAI.Hierarchy.ProtocolRAMCalendarFeedLifetime

namespace OAI
/-! # Authenticating the purchased reserve at the chronological account's entry -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open PurchaseStage
open scoped Classical Fin.CommRing
noncomputable section
variable {w q goods : ℕ} {I : Type*} [Fintype I]

namespace StockCommit

/-- The buy-mode and table observations on the actual label-and-seed run.
These are pre-transfer instruction inputs, including the real gated histogram. -/
structure BuyInput (a : Area) (s : Sources) (g : LabelSource) (b : Batch q goods) (m : Memory w)
    (i : Fin a.goods) : Prop where
  idle : let stamped := (g.pass a.occurrences).apply m
    ∀ e : Fin a.occurrences,RepairHistogram.delta (a.columns s) ((a.seed s).apply stamped) e=0
  bought : let st := fresh a s
    let stamped := (g.pass a.occurrences).apply m
    let raw := RepairHistogram.beforeTransfer st.columns st.plan a.occurrences a.goods
      (st.beforeApply b a.rows ((a.seed s).apply stamped))
    (s.mode.eval raw (i.val:Word w)).val=3
  half : let st := fresh a s
    let stamped := (g.pass a.occurrences).apply m
    let raw := RepairHistogram.beforeTransfer st.columns st.plan a.occurrences a.goods
      (st.beforeApply b a.rows ((a.seed s).apply stamped))
    let old := a.bank.read raw (i.val:Word w)
    (s.half.read raw old).val=old.val/2

end StockCommit

omit [Fintype I] in
theorem AccountColumns.acquired_stock (A : AccountColumns I) (C : Chart w q goods) (mem : Memory w) (p h : ℕ)
    (a : StockCommit.Area) (s : StockCommit.Sources) (g : StockCommit.LabelSource) (b : Batch q goods)
    (i : I) (slot : Fin a.goods) (commit : C.commit (.outer p h)=StockCommit.pricedSegment a s g w b)
    (ready : Calendar.ready C (.attempt (.outer p h)) (trialState C mem p h))
    (safe : protected C (s.old.base+slot.val) (.attempt (.outer p h)))
    (fits : StockCommit.PrefixFits a s b) (room : a.stop<2^w)
    (wide : 4≤2^w) (oldFits : a.goods ≤ s.old.size) (oldBelow : s.old.base+a.goods≤g.out)
    (prior : A.stockAt (.outer p h) i=s.old.base+slot.val)
    (next : A.stockAt (.inner p h 0 0) i=a.output+slot.val)
    (buy : let x := Attempt.outer p h
      StockCommit.BuyInput a s g b (postOutput (C.layout x) (repair C x) (prepared C x (trialState C mem p h))) slot) :
    let old := (A.trial C mem p h).bits i
    (A.inner C mem p h 0 0).bits i=old/2 ∧
      (reserveState C mem p h 0 (a.output+a.goods+slot.val)).val=old-old/2 := by
  let x := Attempt.outer p h
  let start := trialState C mem p h
  let posted := postOutput (C.layout x) (repair C x) (prepared C x start)
  have previous : (posted (s.old.base+slot.val)).val=(A.trial C mem p h).bits i := by
    simpa only [AccountColumns.trial,AccountColumns.read,prior] using
      congrArg Fin.val (postOutput_prior C x start _ ready safe)
  have observed : reserveState C mem p h 0=(StockCommit.pricedSegment a s g w b).after posted := by
    change (C.commit (.outer p h)).after posted=_
    rw [commit]
  rcases ready with ⟨_,_,_,_,_,_,_,_,_,_,done,_,_⟩
  rw [commit] at done
  have pair := StockCommit.priced_buy a s g b posted slot done fits room wide oldFits oldBelow
    buy.idle buy.bought buy.half
  dsimp only
  obtain ⟨keep,ret,_⟩ := pair
  constructor
  · change (reserveState C mem p h 0 (A.stockAt (.inner p h 0 0) i)).val=_
    rw [next,observed,keep,previous]
  · rw [observed,ret,previous]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
