import OAI.Hierarchy.ProtocolRAMNativePriceLabels
import OAI.Hierarchy.ProtocolRAMStockCommitPortSources
import OAI.Hierarchy.ProtocolRAMCalendarCommitPrice
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # Fresh commodity accumulation and immutable chronological stock snapshots -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {w q d : ℕ}

theorem Area.span (a : Area) : a.stop≤a.start+4*a.occurrences+a.rows+8*a.goods+4 := by
  have pad := ProtocolRAMPurchaseSampler.span_le a.goods
  dsimp only [stop,output,excess,clip,src,broadcast,direct,Area.pad]
  omega

theorem columns_ofBatch (a : Area) (old reserve half price owner parity : Bank) (mode slot ball port : Expr)
    (b : Batch q d) (tabs : Fin d → Fin q → Expr) :
    a.columns (Sources.ofBatch old reserve half price owner parity mode slot ball port b tabs)=
      RepairHistogram.fromBatch owner parity (RepairHistogram.destination a.start a.goods slot) ball port b tabs := rfl

theorem Area.seed_read (a : Area) (s : Sources) (m : Memory w) (j : Fin a.goods)
    (width : a.goods≤2^w) (capacity : a.goods≤ s.old.size) :
    (a.seed s).apply m (a.start+j.val)=m (s.old.base+j.val) := by
  rw [show (a.seed s).apply m (a.start+j.val)=(Expr.lookup s.old .row).eval m (j.val:Word w) from
    ProtocolRAMGeneratedWrite.read_image ..]
  simp only [Expr.eval,Bank.read,Fin.val_cast_of_lt (j.isLt.trans_le width),Nat.mod_eq_of_lt (j.isLt.trans_le capacity)]

theorem Area.seed_clock (a : Area) (s : Sources) : (a.seed s).clock=4+18*a.goods := by
  simp [seed,Pass.clock,Expr.work,Nat.mul_comm]

theorem Area.seed_input (a : Area) (s : Sources) (m : Memory w) (e : Expr) (r : Word w)
    (before : e.inputEnd≤a.start) (room : a.start<2^w) : e.eval ((a.seed s).apply m) r=e.eval m r :=
  eval_below _ _ _ _ (e.fits_of_inputEnd before room) (fun x h => a.seed_frame s m x (.inl h))

theorem Area.seed_bank (a : Area) (s : Sources) (m : Memory w) (b : Bank) (r : Word w)
    (before : b.base+b.size≤a.start) : b.read ((a.seed s).apply m) r=b.read m r := by
  have lt := Nat.mod_lt r.val (Nat.two_pow_pos b.bits)
  change r.val%b.size<b.size at lt
  exact a.seed_frame s m _ (.inl (by omega))

theorem freshSegment_ticks (a : Area) (s : Sources) (w : ℕ) (b : Batch q d) :
    (freshSegment a s w b).ticks = 4+18*a.goods + ((fresh a s).native w a.rows b).ticks := by
  change (a.seed s).clock+_=_
  rw [a.seed_clock]

theorem freshSegment_size (a : Area) (s : Sources) (w : ℕ) (b : Batch q d) :
    let p := (freshSegment a s w b).native
    let base := ((fresh a s).native w a.rows b).native
    p.labels=28+base.labels ∧ p.registers=11+base.registers ∧ p.slots=base.slots := by
  have append (tail : Procedure w) :
      (((a.seed s).procedure w).seq tail).labels = 28 + tail.labels ∧
      (((a.seed s).procedure w).seq tail).registers = 11 + tail.registers ∧
      (((a.seed s).procedure w).seq tail).slots = tail.slots := by
    obtain ⟨pc, regs, slots⟩ := scan_size w a.start a.goods (.lookup s.old .row)
    change (scan w a.start a.goods (.lookup s.old .row)).labels + tail.labels = _ ∧
      (scan w a.start a.goods (.lookup s.old .row)).registers + tail.registers = _ ∧
      (scan w a.start a.goods (.lookup s.old .row)).slots + tail.slots = _
    rw [pc, regs, slots, Nat.zero_add]
    exact ⟨rfl, rfl, rfl⟩
  exact append (((fresh a s).native w a.rows b).native)

/-- Every expression supplied by the preceding postFrozen stage reads below the first
fresh word. These are numeric address inequalities that do not depend on the selector. -/
structure PrefixFits (a : Area) (s : Sources) (b : Batch q d) : Prop where
  old : s.old.base+s.old.size≤a.start
  reserve : s.reserve.base+s.reserve.size≤a.start
  half : s.half.base+s.half.size≤a.start
  mode : s.mode.inputEnd≤a.start
  pair : (RepairHistogram.pair (a.columns s)).inputEnd≤a.start
  credit : s.credit.inputEnd≤a.start
  charge : s.charge.inputEnd≤a.start
  slot : s.slot.inputEnd≤a.start
  broadcast : (RepairHistogram.broadcastTerm b s.price).inputEnd≤a.start
  owner : s.owner.base+s.owner.size≤a.start
  parity : s.parity.base+s.parity.size≤a.start

private theorem direct_end (a : Area) (s : Sources) (v : Expr) (fit : v.inputEnd≤a.start) (slot : s.slot.inputEnd≤a.start) :
    (RepairHistogram.ordinaryTerm (a.columns s) (a.plan s) a.goods v).inputEnd≤a.start := by
  simp [RepairHistogram.ordinaryTerm,Area.columns,RepairHistogram.destination,Expr.inputEnd,slot,fit]

/-- Both immutable fee fields survive this segment, including an arbitrary number
of ordinary edges whose signed debits use the same disposable sentinel. -/
theorem eventBoard (a : Area) (s : Sources) (b : Batch q d) (h : PrefixFits a s b) (room : a.stop<2^w) :
    EventBoard (fresh a s) w := by
  obtain ⟨goods,seed,fees,flags,tape,cap,capOut,last⟩ := a.order
  refine ⟨(RepairHistogram.ordinaryTerm (a.columns s) (a.plan s) a.goods s.charge).fits_of_inputEnd (out:=a.direct)
    ((direct_end a s _ h.charge h.slot).trans (by omega)) (by omega),by dsimp [fresh];omega,
    by change a.start+a.goods<2^w;omega,?_⟩
  intro e
  have lt : e.val<a.occurrences := e.isLt
  change RepairHistogram.commit_keeps (a.plan s) a.occurrences a.goods (a.direct+e.val) ∧
    RepairHistogram.commit_keeps (a.plan s) a.occurrences a.goods (a.direct+a.occurrences+e.val)
  simp only [RepairHistogram.commit_keeps,Area.plan,Area.bank]
  exact ⟨⟨by omega,by omega,by omega,by omega⟩,⟨by omega,by omega,by omega,by omega⟩⟩

/-- All layout and active range checks follow from public sizes and the final ceiling.
The single live prerequisite is the immutable ordinal/parity tape from `pairAdvice`. -/
theorem freshSegment_ready (a : Area) (s : Sources) (b : Batch q d) (m : Memory w)
    (h : PrefixFits a s b) (room : a.stop<2^w) (dir : RepairHistogram.PairDirectory (a.columns s) m a.occurrences) :
    (freshSegment a s w b).ready m := by
  obtain ⟨goods,seed,fees,flags,tape,cap,capOut,last⟩ := a.order
  let stock := fresh a s
  let seeded := (a.seed s).apply m
  let u := stock.beforeApply b a.rows seeded
  have ord : stock.direct≤ stock.broadcast := by change a.direct≤a.broadcast;omega
  have low (x : ℕ) (hx : x<a.start) : u x=m x :=
    (stock.beforeCore (rows:=a.rows) b seeded ord x (by change x<a.direct;omega)).trans (a.seed_frame s m x (.inl hx))
  have read (bank : Bank) (below : bank.base+bank.size≤a.start) (r : Word w) : bank.read u r=bank.read m r := by
    unfold Bank.read
    have small := Nat.mod_lt r.val (Nat.two_pow_pos bank.bits)
    exact low _ (by change r.val%bank.size<bank.size at small;omega)
  have mounted : RepairHistogram.PairDirectory (a.columns s) u a.occurrences :=
    ⟨fun i => (read s.parity h.parity _).trans (dir.first i),fun i => (read s.parity h.parity _).trans_ne (dir.second i),
     fun i => (read s.owner h.owner _).trans (dir.firstRow i),fun i => (read s.owner h.owner _).trans (dir.secondRow i)⟩
  have target (e : Fin a.occurrences) : a.start≤RepairHistogram.address (a.columns s) u e ∧
      RepairHistogram.address (a.columns s) u e≤a.start+a.goods := by
    have eqn : RepairHistogram.address (a.columns s) u e =
        a.start + min (s.slot.eval u (e.val:Word w)).val a.goods :=
      RepairHistogram.destination_val _ _ _ _ _ (by omega)
    rw [eqn]
    have := min_le_right (s.slot.eval u (e.val:Word w)).val a.goods
    omega
  have cEnd := direct_end a s _ h.credit h.slot
  have dEnd := direct_end a s _ h.charge h.slot
  have oEnd : (Expr.lookup s.old .row).inputEnd≤a.start := by simpa [Expr.inputEnd] using h.old
  refine ⟨(a.seed s).fits_of_span oEnd (by change a.start+a.goods<2^w;omega),?_,?_,target⟩
  · intro p hp
    change p∈(RepairHistogram.directColumns a.direct a.occurrences a.goods (a.plan s) (a.columns s) ++ [_]) at hp
    simp only [RepairHistogram.directColumns,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (rfl | rfl) | rfl
    · exact Pass.fits_of_span _ (cEnd.trans (by change a.start≤a.direct; omega)) (by change a.direct+a.occurrences<2^w; omega)
    · exact Pass.fits_of_span _ (dEnd.trans (by change a.start≤a.direct+a.occurrences; omega)) (by change a.direct+a.occurrences+a.occurrences<2^w; omega)
    · exact Pass.fits_of_span _ (h.broadcast.trans (by change a.start≤a.broadcast; omega)) (by change a.broadcast+a.rows<2^w; omega)
  · refine ⟨mounted,(RepairHistogram.pair (a.columns s)).fits_of_inputEnd (out:=a.src) (h.pair.trans (by omega)) (by omega),
      by change a.src+2*a.occurrences<2^w;omega,fun e => ?_,?_,?_,?_,?_⟩
    · change RepairHistogram.address (a.columns s) u e<a.src
      exact (target e).2.trans_lt (by omega)
    · change (Expr.lookup a.bank .row).inputEnd≤a.clip
      simp only [Expr.inputEnd,max_zero,Area.bank,Bank.size]
      change a.start+a.pad≤a.clip
      omega
    · change a.clip+a.goods+a.goods<2^w
      omega
    · intro p hp
      change p∈RepairHistogram.transfers (a.plan s) a.goods at hp
      simp only [RepairHistogram.transfers,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl <;> apply Expr.fits_of_inputEnd (out:=a.output) _ _ (by omega)
      all_goals
        simp only [RepairHistogram.retainedTerm,RepairHistogram.reserveTerm,RepairHistogram.excessTerm,
          Area.plan,Area.bank,Expr.inputEnd,Bank.size,max_le_iff];
          have hr := h.reserve; have hh := h.half; have hm := h.mode;
          change s.reserve.base + 2^s.reserve.bits≤a.start at hr;
          change s.half.base + 2^s.half.bits≤a.start at hh;
          change a.goods < 2^ProtocolRAMPurchaseSampler.bits a.goods at goods;
          change a.start+2^ProtocolRAMPurchaseSampler.bits a.goods=a.direct at seed;
          change a.excess+2^ProtocolRAMPurchaseSampler.bits a.goods=a.output at capOut; omega
    · change a.output+a.goods+a.goods+a.goods<2^w
      omega

/-- Obtain the previous stock at a fresh coordinate, before any signed scatter changes
it. A neighboring reserve word in the previous snapshot is never the dummy cell. -/
theorem previous_stock (a : Area) (s : Sources) (m : Memory w) (j : Fin a.goods)
    (room : a.stop<2^w) (old : a.goods≤ s.old.size) :
    ((a.seed s).apply m (((fresh a s).plan.bank.base)+j.val)).val=(m (s.old.base+j.val)).val := by
  obtain ⟨goods,seed,fees,flags,tape,cap,capOut,last⟩ := a.order
  exact congrArg Fin.val (a.seed_read s m j (by omega) old)


end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
