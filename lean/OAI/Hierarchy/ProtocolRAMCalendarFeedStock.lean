import OAI.Hierarchy.ProtocolRAMCalendarFeedRead
import OAI.Hierarchy.ProtocolRAMFeedAmounts
import OAI.Hierarchy.ProbeCommodityBounds
import OAI.Hierarchy.ProbeRepairReplayAccount

namespace OAI
/-! # Native clip and spill outputs at the outer and reserve boundaries -/

namespace Hierarchy.ProtocolRAM.Calendar.FeedLayout

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open AdaptiveProbe
open scoped Fin.CommRing Classical
noncomputable section
variable {w q d h N k : ℕ} (L : FeedLayout h N k)
abbrev Good (h N k : ℕ) := Commodity (Fin (2^h)) N k

theorem source_stock (base : ℕ) (i : Good h N k) (m : Memory w) (rows : 2^h≤2^w) :
    ((source (h:=h) base (laneOf i)).eval m ((PurchaseInventory.record i).val:Word w)).val=
      PurchaseInventory.stock base m i := by
  have hi := (PurchaseInventory.record i).isLt
  simp [source,Expr.eval,Bank.read,Bank.size,Fin.val_cast_of_lt (hi.trans_le rows),Nat.mod_eq_of_lt hi,
    PurchaseInventory.stock,PurchaseInventory.slot,laneOf,Nat.add_assoc]

theorem slice_le_total {steps j : ℕ} (bits : ℕ) (live : j<steps) : slice steps bits j≤bits := by
  have all := slice_sum steps bits (by omega)
  exact (Finset.single_le_sum (fun t _=>Nat.zero_le (slice steps bits t)) (Finset.mem_range.mpr live)).trans_eq all

/-- A capped live stock and one ordinary payload fit the input adder. -/
theorem outer_word_room {stock width steps j cap : ℕ} (i : Good h N k) (old : stock ≤ cap*width)
    (fits : (cap+1)*width<2^w) :
    stock+(if j<steps then slice steps width j*payloadUnit i else 0)<2^w := by
  rw [Nat.add_mul,Nat.one_mul] at fits
  by_cases live : j<steps
  · have sliced := slice_le_total width live
    cases i <;> simp only [ite_eq_left live,payloadUnit,Nat.mul_one,Nat.mul_zero] <;> omega
  · simp only [ite_eq_right live,Nat.add_zero]
    omega

/-- The purchased reserve is a part of the entry stock. Even all its bits
delivered in one interval fit in the same fixed machine word. -/
theorem reserve_word_room {stock reserve width steps j cap : ℕ} {buy : Prop} [Decidable buy]
    (live : j<steps) (old : stock ≤ cap*width) (saved : reserve ≤ cap*width)
    (fits : 2*(cap*width)<2^w) :
    stock+(if buy then slice steps reserve j else 0)<2^w := by
  have sliced := slice_le_total reserve live
  split <;> omega

private theorem outer_amount (c : Mesh) (p : ℕ) (i : Good h N k) :
    (L.column (laneOf i)).outerAmount c p =
      if p<c.inject then slice c.inject L.width p*payloadUnit i else 0 := by
  cases i with
  | inl a =>
    simp [CommodityColumn.outerAmount,column,laneOf,PurchaseInventory.lane,payloadUnit]
  | inr a =>
    simp [CommodityColumn.outerAmount,column,laneOf,PurchaseInventory.lane,payloadUnit,slice,delivered]

theorem outer_rows (C : Chart w q d) (p : ℕ) (m : Memory w) (placed : C.columns (.outer p)=L.columns)
    (before : L.Before C.mesh C.modeAt (.outer p)) (fits : L.stop<2^w) (capFits : L.cap*L.width<2^w)
    (rows : 2^h≤2^w) (i : Good h N k)
    (room : PurchaseInventory.stock L.active m i+
      (if p<C.mesh.inject then slice C.mesh.inject L.width p*payloadUnit i else 0)<2^w) :
    let bits := PurchaseInventory.stock L.active m i+
      if p<C.mesh.inject then slice C.mesh.inject L.width p*payloadUnit i else 0
    let out := after C (.feed (.outer p)) m
    (out (L.kept+PurchaseInventory.slot i)).val=min bits (L.cap*L.width) ∧
    (out (L.overflow+PurchaseInventory.slot i)).val=bits-min bits (L.cap*L.width) := by
  let f := L.column (laneOf i)
  let r := ((PurchaseInventory.record i).val:Word w)
  have stock : (f.stock.eval m r).val=PurchaseInventory.stock L.active m i :=
    source_stock L.active i m rows
  have amount := L.outer_amount C.mesh p i
  have unclip := f.outer_total C.mesh p C.modeAt m r (by simpa only [stock,amount,f] using room)
  rw [stock,amount] at unclip
  dsimp only [f,r] at unclip
  simpa only [unclip] using L.read C (.outer p) m placed before fits capFits i

/-- Here the archived mode word and the original retained reserve are both read
from the live chronological memory. Its public ROM supplies exactly the floor slice. -/
theorem inner_rows (C : Chart w q d) (p a j : ℕ) (m fixture : Memory w)
    (placed : C.columns (.inner p a j)=L.columns) (before : L.Before C.mesh C.modeAt (.inner p a j))
    (fits : L.stop<2^w) (capFits : L.cap*L.width<2^w) (rows : 2^h≤2^w) (i : Good h N k)
    (index : j<C.mesh.reserveSteps) (digit : PurchaseInventory.stock L.saved m i<L.stride)
    (size : C.mesh.reserveSteps*L.stride≤L.table.size) (limit : C.mesh.reserveSteps*L.stride<2^w)
    (mounted : ∀ x,L.table.base≤x → x<L.table.base+C.mesh.reserveSteps*L.stride →
      m x=feedAdvice L.table C.mesh.reserveSteps L.stride fixture x)
    (room : PurchaseInventory.stock L.active m i+
      (if m (C.modeAt (.outer p a))=3 then slice C.mesh.reserveSteps (PurchaseInventory.stock L.saved m i) j else 0)<2^w) :
    let bits := PurchaseInventory.stock L.active m i+
      if m (C.modeAt (.outer p a))=3 then slice C.mesh.reserveSteps (PurchaseInventory.stock L.saved m i) j else 0
    let out := after C (.feed (.inner p a j)) m
    (out (L.kept+PurchaseInventory.slot i)).val=min bits (L.cap*L.width) ∧
    (out (L.overflow+PurchaseInventory.slot i)).val=bits-min bits (L.cap*L.width) := by
  let f := L.column (laneOf i)
  let r := ((PurchaseInventory.record i).val:Word w)
  have stock : (f.stock.eval m r).val=PurchaseInventory.stock L.active m i :=
    source_stock L.active i m rows
  have saved : (f.reserve.eval m r).val=PurchaseInventory.stock L.saved m i :=
    source_stock L.saved i m rows
  have raw := f.inner_total C.mesh p a j C.modeAt m r fixture index (by rwa [saved]) size limit mounted
    (by simpa only [stock,CommodityColumn.innerAmount,saved] using room)
  rw [stock,CommodityColumn.innerAmount,saved] at raw
  dsimp only [f,r] at raw
  simpa only [raw] using L.read C (.inner p a j) m placed before fits capFits i

theorem idle_rows (C : Chart w q d) (p a j : ℕ) (m : Memory w)
    (placed : C.columns (.inner p a j)=L.columns) (before : L.Before C.mesh C.modeAt (.inner p a j))
    (fits : L.stop<2^w) (capFits : L.cap*L.width<2^w) (rows : 2^h≤2^w) (i : Good h N k)
    (idle : m (C.modeAt (.outer p a))≠3) (bounded : PurchaseInventory.stock L.active m i≤L.cap*L.width) :
    let out := after C (.feed (.inner p a j)) m
    (out (L.kept+PurchaseInventory.slot i)).val=PurchaseInventory.stock L.active m i ∧
    (out (L.overflow+PurchaseInventory.slot i)).val=0 := by
  have amount := (L.column (laneOf i)).inner_idle C.mesh p a j C.modeAt m
    ((PurchaseInventory.record i).val:Word w) idle
  have stock := source_stock L.active i m rows
  change (((L.column (laneOf i)).stock).eval m ((PurchaseInventory.record i).val:Word w)).val=_ at stock
  simpa only [amount,stock,min_eq_left bounded,Nat.sub_self] using
    L.read C (.inner p a j) m placed before fits capFits i

/-- Reading the designated stock array at the next outer trial gives the requested
boundary stock; the other bank supplies the delta of the signed receipt. -/
theorem stored (A : AccountColumns (Good h N k)) (C : Chart w q d) (p : ℕ) (mem : Memory w)
    (placed : C.columns (.outer p)=L.columns) (before : L.Before C.mesh C.modeAt (.outer p))
    (fits : L.stop<2^w) (capFits : L.cap*L.width<2^w) (rows : 2^h≤2^w) (i : Good h N k)
    (width : A.payloadWidth=L.width) (payload : A.payload i=payloadUnit i)
    (prior : A.stockAt (.outer p C.mesh.outerFuel) i=L.active+PurchaseInventory.slot i)
    (next : A.stockAt (.outer (p+1) 0) i=L.kept+PurchaseInventory.slot i)
    (room : A.bank.requests A.payloadWidth C.mesh.inject p (A.trial C mem p C.mesh.outerFuel) i<2^w) :
    let bits := A.bank.requests A.payloadWidth C.mesh.inject p (A.trial C mem p C.mesh.outerFuel)
    (A.trial C mem (p+1) 0).bits i=min (bits i) (L.cap*A.payloadWidth) ∧
    ((phaseState C mem (p+1)) (L.overflow+PurchaseInventory.slot i)).val=
      spillBits L.cap A.payloadWidth bits i := by
  have req : A.bank.requests A.payloadWidth C.mesh.inject p (A.trial C mem p C.mesh.outerFuel) i =
      PurchaseInventory.stock L.active (trialState C mem p C.mesh.outerFuel) i+
        if p<C.mesh.inject then slice C.mesh.inject L.width p*payloadUnit i else 0 := by
    simp [OuterBank.requests,AccountColumns.bank,AccountColumns.trial,AccountColumns.read,
      prior,payload,width,PurchaseInventory.stock]
  have check := L.outer_rows C p (trialState C mem p C.mesh.outerFuel) placed before fits capFits rows i
    (req ▸ room)
  dsimp only
  unfold spillBits clipBits
  rw [req,width]
  constructor
  · change ((trialState C mem (p+1) 0) (A.stockAt (.outer (p+1) 0) i)).val=_
    rw [trial_zero,phase_succ,next]
    exact check.1
  · rw [phase_succ]
    exact check.2

/-- The complete public instruction prefix that reaches a particular current inner trial. -/
def beforeInner (c : Mesh) (p a j b : ℕ) : List Event :=
  (List.range p).flatMap (outerBlock c) ++ (List.range a).flatMap (trialBlock c p) ++
  [.attempt (.outer p a)] ++ purchaseTail c p a j b

theorem inner_as_run (C : Chart w q d) (m : Memory w) (p a j b : ℕ) :
    innerState C m p a j b=run C (beforeInner C.mesh p a j b) m := by
  simp only [beforeInner,purchaseTail,run_append,run]
  rfl

/-- Load the floor ROM once before the initial calendar, and read it from the
chronological memory after all earlier attempts and boundaries. -/
theorem rom_from_initial (C : Chart w q d) (fixture : Memory w) (p a j b : ℕ)
    (installed : Calendar.mounted C (beforeInner C.mesh p a j b) (feedAdvice L.table C.mesh.reserveSteps L.stride fixture))
    (safe : ∀ x,L.table.base≤x → x<L.table.base+C.mesh.reserveSteps*L.stride →
      ∀ e∈beforeInner C.mesh p a j b,protected C x e) :
    ∀ x,L.table.base≤x → x<L.table.base+C.mesh.reserveSteps*L.stride →
      innerState C (feedAdvice L.table C.mesh.reserveSteps L.stride fixture) p a j b x =
        feedAdvice L.table C.mesh.reserveSteps L.stride fixture x := by
  intro x h₀ h₁
  rw [inner_as_run]
  exact run_frame C _ _ x installed (safe x h₀ h₁)

/-- A protected reserve word belongs to the same original acquisition across every repair
and every feed in its interval. This also applies to the archived mode word. -/
theorem at_boundary (C : Chart w q d) (mem : Memory w) (p a j x : ℕ)
    (mounted : Calendar.mounted C (purchaseTail C.mesh p a j C.mesh.innerFuel) (reserveState C mem p a 0))
    (safe : ∀ e∈purchaseTail C.mesh p a j C.mesh.innerFuel, protected C x e) :
    innerState C mem p a j C.mesh.innerFuel x=reserveState C mem p a 0 x :=
  purchase_archive C mem p a j C.mesh.innerFuel x mounted safe

/-- The retained and overflow fields in a purchased replay use the authenticated
entry reserve, computed once by the acquisition and untouched throughout its inner loop. -/
theorem retained (A : AccountColumns (Good h N k)) (C : Chart w q d) (mem fixture : Memory w) (p a j : ℕ)
    (placed : C.columns (.inner p a j)=L.columns) (before : L.Before C.mesh C.modeAt (.inner p a j))
    (fits : L.stop<2^w) (capFits : L.cap*L.width<2^w) (rows : 2^h≤2^w) (i : Good h N k)
    (index : j<C.mesh.reserveSteps) (width : A.payloadWidth=L.width)
    (prior : A.stockAt (.inner p a j C.mesh.innerFuel) i=L.active+PurchaseInventory.slot i)
    (next : A.stockAt (.inner p a (j+1) 0) i=L.kept+PurchaseInventory.slot i)
    (purchase : reserveState C mem p a 0 (C.modeAt (.outer p a))=3)
    (original : PurchaseInventory.stock L.saved (reserveState C mem p a 0) i=
      (A.trial C mem p a).bits i-(A.trial C mem p a).bits i/2)
    (mounted : Calendar.mounted C (purchaseTail C.mesh p a j C.mesh.innerFuel) (reserveState C mem p a 0))
    (archived : ∀ e∈purchaseTail C.mesh p a j C.mesh.innerFuel,
      protected C (C.modeAt (.outer p a)) e ∧ protected C (L.saved+PurchaseInventory.slot i) e)
    (digit : (A.trial C mem p a).bits i-(A.trial C mem p a).bits i/2<L.stride)
    (size : C.mesh.reserveSteps*L.stride≤L.table.size) (limit : C.mesh.reserveSteps*L.stride<2^w)
    (rom : ∀ x,L.table.base≤x → x<L.table.base+C.mesh.reserveSteps*L.stride →
      innerState C mem p a j C.mesh.innerFuel x=feedAdvice L.table C.mesh.reserveSteps L.stride fixture x)
    (room : A.bank.replayFeed C.mesh.reserveSteps j (A.trial C mem p a) (A.inner C mem p a j C.mesh.innerFuel) i<2^w) :
    let bits := A.bank.replayFeed C.mesh.reserveSteps j (A.trial C mem p a) (A.inner C mem p a j C.mesh.innerFuel)
    (A.inner C mem p a (j+1) 0).bits i=min (bits i) (L.cap*A.payloadWidth) ∧
    (reserveState C mem p a (j+1) (L.overflow+PurchaseInventory.slot i)).val=
      spillBits L.cap A.payloadWidth bits i := by
  let m := innerState C mem p a j C.mesh.innerFuel
  have mode : m (C.modeAt (.outer p a))=3 :=
    (at_boundary C mem p a j _ mounted (fun e he=>(archived e he).1)).trans purchase
  have saved : PurchaseInventory.stock L.saved m i=(A.trial C mem p a).bits i-(A.trial C mem p a).bits i/2 :=
    (congrArg Fin.val (at_boundary C mem p a j _ mounted (fun e he=>(archived e he).2))).trans original
  have active : PurchaseInventory.stock L.active m i=(A.inner C mem p a j C.mesh.innerFuel).bits i := by
    simp [AccountColumns.inner,AccountColumns.read,prior,PurchaseInventory.stock,m]
  have req : A.bank.replayFeed C.mesh.reserveSteps j (A.trial C mem p a) (A.inner C mem p a j C.mesh.innerFuel) i=
      PurchaseInventory.stock L.active m i+(if m (C.modeAt (.outer p a))=3 then
        slice C.mesh.reserveSteps (PurchaseInventory.stock L.saved m i) j else 0) := by
    simp [OuterBank.replayFeed,AccountColumns.bank,active,mode,saved]
  have check := L.inner_rows C p a j m fixture placed before fits capFits rows i index
    (by rwa [saved]) size limit rom (req ▸ room)
  dsimp only
  unfold spillBits clipBits
  rw [req,width]
  constructor
  · change ((innerState C mem p a (j+1) 0) (A.stockAt (.inner p a (j+1) 0) i)).val=_
    rw [inner_zero,reserve_succ,next]
    exact check.1
  · rw [reserve_succ]
    exact check.2

end
end Hierarchy.ProtocolRAM.Calendar.FeedLayout

end OAI
