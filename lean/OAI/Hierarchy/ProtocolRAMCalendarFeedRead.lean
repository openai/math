import OAI.Hierarchy.ProtocolRAMDisjointPassReads
import OAI.Hierarchy.ProtocolRAMCalendarInventory
import OAI.Hierarchy.ProtocolRAMPurchaseInventory

namespace OAI
/-! # Native calendar feed columns and the retained and discharged bits they write -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical

variable {w q d h N k : ℕ}

/-- The first bank in each dense inventory holds the payload. The remaining banks
have the same stage and signed-axis order as the frozen price scan. -/
structure FeedLayout (h N k : ℕ) where
  active : ℕ
  saved : ℕ
  kept : ℕ
  width : ℕ
  cap : ℕ
  table : Bank
  stride : ℕ

namespace FeedLayout
variable (L : FeedLayout h N k)

abbrev lanes (N k : ℕ) := 1+N*(2*k)
def overflow := L.kept+PurchaseInventory.footprint h N k
def stop := L.overflow+PurchaseInventory.footprint h N k

def source {h : ℕ} (base : ℕ) (l : Fin (lanes N k)) : Expr :=
  .lookup ⟨base+l.val*2^h,h⟩ .row

def column (l : Fin (lanes N k)) : CommodityColumn :=
  ⟨2^h,L.cap*L.width,source (h:=h) L.active l,source (h:=h) L.saved l,
    L.table,L.stride,if l.val=0 then L.width else 0,
    L.kept+l.val*2^h,L.overflow+l.val*2^h⟩

def columns : List CommodityColumn := (List.finRange (lanes N k)).map L.column

def block (l : Fin (lanes N k)) (spill : Bool) : ℕ :=
  if spill then lanes N k+l.val else l.val

def pass (c : Mesh) (addr : Attempt→ℕ) (b : Boundary) (l : Fin (lanes N k)) (spill : Bool) : Pass :=
  let f := (L.column l).feed c b
  ⟨L.kept+block l spill*2^h,2^h,
    if spill then StockAccounts.overflow (L.cap*L.width) (total addr b f)
    else StockAccounts.clipped (L.cap*L.width) (total addr b f)⟩

theorem passes_eq (c : Mesh) (addr : Attempt→ℕ) (b : Boundary) (l : Fin (lanes N k)) :
    ((L.column l).feed c b).passes addr b=[L.pass c addr b l false,L.pass c addr b l true] := by
  simp [pass,block,Feed.passes,CommodityColumn.feed,column,overflow,PurchaseInventory.footprint,
    lanes,Nat.add_mul,Nat.add_assoc]

private theorem separated {l l' : Fin (lanes N k)} {t t' : Bool} (hne : l≠l' ∨ t≠t') :
    block l t≠block l' t' := by
  have hi := l.isLt
  have hi' := l'.isLt
  intro eq
  cases t <;> cases t' <;> simp only [block,Bool.false_eq_true,ite_false,ite_true] at eq
  · exact (hne.resolve_right (by simp)) (Fin.ext eq)
  · omega
  · omega
  · exact (hne.resolve_right (by simp)) (Fin.ext (by omega))

private theorem intervals (c : Mesh) (addr : Attempt→ℕ) (b : Boundary)
    {l l' : Fin (lanes N k)} {t t' : Bool} (hne : l≠l' ∨ t≠t') :
    let p := L.pass c addr b l t
    let s := L.pass c addr b l' t'
    p.out+p.rows ≤ s.out ∨ s.out+s.rows ≤ p.out := by
  obtain lt|gt := lt_or_gt_of_ne (separated hne)
  · left
    have z := Nat.mul_le_mul_right (2^h) lt
    simp only [Nat.succ_mul] at z
    change L.kept+block l t*2^h+2^h≤L.kept+block l' t'*2^h
    omega
  · right
    have z := Nat.mul_le_mul_right (2^h) gt
    simp only [Nat.succ_mul] at z
    change L.kept+block l' t'*2^h+2^h≤L.kept+block l t*2^h
    omega

def schedule (c : Mesh) (addr : Attempt→ℕ) (b : Boundary) : List Pass :=
  (List.finRange (lanes N k)).flatMap fun l=>[L.pass c addr b l false,L.pass c addr b l true]

theorem generated (C : Chart w q d) (b : Boundary) (placed : C.columns b=L.columns) :
    feedPasses C b=L.schedule C.mesh C.modeAt b := by
  simp [feedPasses,placed,columns,schedule,List.flatMap_map,L.passes_eq]

private theorem order (c : Mesh) (addr : Attempt→ℕ) (b : Boundary) :
    (L.schedule c addr b).Pairwise (fun p s=>p.out+p.rows ≤ s.out ∨ s.out+s.rows ≤ p.out) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro l _
    simpa using L.intervals c addr b (l:=l) (l':=l) (t:=false) (t':=true) (Or.inr (by decide))
  · apply (List.nodup_finRange (lanes N k)).imp
    intro l l' hn p hp s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp hs
    rcases hp with rfl|rfl <;> rcases hs with rfl|rfl <;> exact L.intervals c addr b (Or.inl hn)

/-- Only the three input banks and the one remembered acquisition mode are read by a
feed. They precede both output arrays. -/
structure Before (c : Mesh) (addr : Attempt → ℕ) (b : Boundary) : Prop where
  active : L.active+PurchaseInventory.footprint h N k ≤ L.kept
  saved : L.saved+PurchaseInventory.footprint h N k ≤ L.kept
  advice : L.table.base+L.table.size ≤ L.kept
  mode : ∀ p t j,b=.inner p t j → addr (.outer p t)+1≤L.kept

private theorem source_end (base : ℕ) (l : Fin (lanes N k)) :
    (source (h:=h) base l).inputEnd≤base+PurchaseInventory.footprint h N k := by
  have big := Nat.mul_le_mul_right (2^h) l.isLt
  simp only [Nat.succ_mul] at big
  simpa only [source,Expr.inputEnd,max_zero,Bank.size,PurchaseInventory.footprint,lanes,Nat.add_assoc]
    using Nat.add_le_add_left big base

private theorem pass_end (c : Mesh) (addr : Attempt→ℕ) (b : Boundary)
    (before : L.Before c addr b) (l : Fin (lanes N k)) (t : Bool) :
    (L.pass c addr b l t).term.inputEnd ≤ L.kept := by
  have active := (source_end (h:=h) L.active l).trans before.active
  have saved := (source_end (h:=h) L.saved l).trans before.saved
  have advice := before.advice
  cases b with
  | outer p =>
    cases t <;> simp [pass,StockAccounts.clipped,StockAccounts.overflow,total,onBoundary,
      CommodityColumn.feed,column,Expr.inputEnd,active]
  | inner p a j =>
    have mode := before.mode p a j rfl
    cases t <;> simp [pass,StockAccounts.clipped,StockAccounts.overflow,total,onBoundary,
      CommodityColumn.feed,column,word,Expr.inputEnd,Bank.size,active,saved,mode] at * <;> exact advice

private theorem mem_schedule (c : Mesh) (addr : Attempt→ℕ) (b : Boundary) (p : Pass) :
    p∈L.schedule c addr b ↔ ∃ l t,p=L.pass c addr b l t := by
  simp only [schedule,List.mem_flatMap,List.mem_finRange,true_and,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro ⟨l,h|h⟩
    · exact ⟨l,false,h⟩
    · exact ⟨l,true,h⟩
  · rintro ⟨l,t,rfl⟩
    refine ⟨l, ?_⟩
    cases t with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl

theorem safe_below (C : Chart w q d) (b : Boundary) (placed : C.columns b=L.columns) (x : ℕ)
    (early : x<L.kept) : protected C x (.feed b) := by
  intro p hp
  rw [L.generated C b placed] at hp
  obtain ⟨l,t,rfl⟩ := (L.mem_schedule ..).mp hp
  exact early.trans_le (Nat.le_add_right ..)

theorem schedule_length (c : Mesh) (addr : Attempt→ℕ) (b : Boundary) :
    (L.schedule c addr b).length=2*lanes N k := by
  have count (ls : List (Fin (lanes N k))) :
      (ls.flatMap (fun l=>[L.pass c addr b l false,L.pass c addr b l true])).length=2*ls.length := by
    induction ls with
    | nil => simp
    | cons l ls ih => simp [ih,Nat.mul_add,Nat.add_comm]; omega
  simpa [schedule] using count (List.finRange (lanes N k))

theorem schedule_work (c : Mesh) (addr : Attempt→ℕ) (b : Boundary) {p : Pass}
    (member : p∈L.schedule c addr b) : p.rows=2^h ∧ p.term.work≤100 := by
  obtain ⟨l,t,rfl⟩ := (L.mem_schedule ..).mp member
  constructor
  · rfl
  · cases b <;> cases t <;>
      norm_num [pass,StockAccounts.clipped,StockAccounts.overflow,total,onBoundary,CommodityColumn.feed,
        column,source,word,Expr.work]

theorem ticks_le (C : Chart w q d) (b : Boundary) (placed : C.columns b=L.columns) :
    ticks C (.feed b)≤4+2*lanes N k*(4+2^h*204) := by
  change clock (feedPasses C b)≤_
  rw [L.generated C b placed]
  simpa only [L.schedule_length] using
    clock_le (L.schedule C.mesh C.modeAt b) (2^h) 100
      (fun _ hp=>⟨(L.schedule_work _ _ _ hp).1.le,(L.schedule_work _ _ _ hp).2⟩)

private theorem extent (c : Mesh) (addr : Attempt→ℕ) (b : Boundary)
    (l : Fin (lanes N k)) (t : Bool) :
    (L.pass c addr b l t).out+(L.pass c addr b l t).rows≤L.stop := by
  have hi := l.isLt
  have bd : block l t < lanes N k+lanes N k := by cases t <;> simp [block]; omega
  have z : (block l t+1)*2^h≤(lanes N k+lanes N k)*2^h :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt bd)
  change L.kept+block l t*2^h+2^h≤L.kept+lanes N k*2^h+(lanes N k)*2^h
  simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using Nat.add_le_add_left z L.kept

theorem generated_extent (C : Chart w q d) (b : Boundary) (placed : C.columns b=L.columns)
    (p : Pass) (hp : p∈feedPasses C b) : p.out+p.rows≤L.stop := by
  rw [L.generated C b placed] at hp
  obtain ⟨l,t,rfl⟩ := (L.mem_schedule ..).mp hp
  exact L.extent _ _ _ l t

theorem ready (C : Chart w q d) (b : Boundary) (m : Memory w) (placed : C.columns b=L.columns)
    (before : L.Before C.mesh C.modeAt b) (fits : L.stop<2^w) : Calendar.ready C (.feed b) m := by
  intro p hp
  rw [L.generated C b placed] at hp
  obtain ⟨l,t,rfl⟩ := (L.mem_schedule _ _ _ _).mp hp
  apply Pass.fits_of_span
  · exact (L.pass_end _ _ _ before l t).trans (Nat.le_add_right ..)
  · exact (L.extent _ _ _ l t).trans_lt fits

/-- Both physical output arrays contain the result of evaluating the same
pre-feed stock expression on the original input, including every archived key. -/
theorem lane_read (C : Chart w q d) (b : Boundary) (m : Memory w) (placed : C.columns b=L.columns)
    (before : L.Before C.mesh C.modeAt b) (fits : L.stop<2^w) (capFits : L.cap*L.width<2^w)
    (l : Fin (lanes N k)) (i : Fin (2^h)) :
    let old := ((total C.modeAt b ((L.column l).feed C.mesh b)).eval m (i.val:Word w)).val
    ((after C (.feed b) m) (L.kept+l.val*2^h+i.val)).val=min old (L.cap*L.width) ∧
    ((after C (.feed b) m) (L.overflow+l.val*2^h+i.val)).val=old-min old (L.cap*L.width) := by
  let rd (t : Bool) := L.pass C.mesh C.modeAt b l t
  have wide : L.kept<2^w := (show L.kept≤L.stop by unfold stop overflow; omega).trans_lt fits
  have part (t : Bool) : result (L.schedule C.mesh C.modeAt b) m ((rd t).out+i.val)=
      (rd t).term.eval m (i.val:Word w) := by
    apply scheduled_read _ m (rd t) ((L.mem_schedule ..).mpr ⟨l,t,rfl⟩) i L.kept
    · exact (rd t).term.fits_of_inputEnd (L.pass_end C.mesh C.modeAt b before l t) wide
    · intro s hs
      obtain ⟨l',t',rfl⟩ := (L.mem_schedule ..).mp hs
      exact Nat.le_add_right ..
    · exact L.order ..
  have keep := (congrArg Fin.val (part false)).trans (StockAccounts.clipped_word _ _ _ _ capFits)
  have spill := (congrArg Fin.val (part true)).trans (StockAccounts.overflow_word _ _ _ _ capFits)
  simpa [after,L.generated C b placed,rd,pass,block,overflow,PurchaseInventory.footprint,
    lanes,Nat.add_assoc,Nat.add_mul] using And.intro keep spill

noncomputable def laneOf (i : AdaptiveProbe.Commodity (Fin (2^h)) N k) : Fin (lanes N k) :=
  ⟨PurchaseInventory.lane i,PurchaseInventory.lane_lt i⟩

theorem read (C : Chart w q d) (b : Boundary) (m : Memory w) (placed : C.columns b=L.columns)
    (before : L.Before C.mesh C.modeAt b) (fits : L.stop<2^w) (capFits : L.cap*L.width<2^w)
    (i : AdaptiveProbe.Commodity (Fin (2^h)) N k) :
    let z := PurchaseInventory.record i
    let bits := ((total C.modeAt b ((L.column (laneOf i)).feed C.mesh b)).eval m (z.val:Word w)).val
    ((after C (.feed b) m) (L.kept+PurchaseInventory.slot i)).val=min bits (L.cap*L.width) ∧
    ((after C (.feed b) m) (L.overflow+PurchaseInventory.slot i)).val=bits-min bits (L.cap*L.width) := by
  simpa only [laneOf,PurchaseInventory.slot,Nat.add_assoc] using
    L.lane_read C b m placed before fits capFits (laneOf i) (PurchaseInventory.record i)

/-- Clipping bounds the new active stock for every commodity, independently of
the saved words, the input stock, and the correctness of any higher charge view. -/
theorem bounded (C : Chart w q d) (b : Boundary) (m : Memory w) (placed : C.columns b=L.columns)
    (before : L.Before C.mesh C.modeAt b) (fits : L.stop<2^w) (capFits : L.cap*L.width<2^w)
    (i : AdaptiveProbe.Commodity (Fin (2^h)) N k) :
    ((after C (.feed b) m) (L.kept+PurchaseInventory.slot i)).val≤L.cap*L.width :=
  (L.read C b m placed before fits capFits i).1.le.trans (Nat.min_le_right _ _)

end FeedLayout
end Hierarchy.ProtocolRAM.Calendar

end OAI
