import OAI.Computability.BorderVNP.CubeISAOwnedSingleRowModel

/-! # Actual native scatter through the full singleton-candidate row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.SingleRowData

open RoutingISA RoutingISA.Owned Physical Physical.Owned VPVNP.BurstRAM DiagonalResidueRAM Finset

variable {w n d len : ℕ} (D : SingleRowData n d len)

/-- Fixed ABI of the singleton-row loop on entry. -/
structure Entry (s : Bank w) : Prop where
  /-- Constant zero. -/
  zero : readings s 0 = 0
  /-- Unit word used by the trial counter. -/
  one : readings s 1 = 1
  /-- Symbol alphabet. -/
  radix : readings s 10 = d
  /-- Number of complete tails after fixing one coordinate. -/
  tails : readings s 11 = d^n
  /-- Place value of the grouping symbol. -/
  place : readings s 12 = d^D.axis.val
  /-- Ordered source symbol. -/
  left : readings s 14 = D.left.val
  /-- Ordered destination symbol. -/
  right : readings s 15 = D.right.val
  /-- Starting trial index. -/
  start : readings s 18 = 0
  /-- Number of ordered pair trials. -/
  bound : readings s 19 = singlePairTrials n d
  /-- Width of one singleton interval. -/
  width : readings s 21 = len
  /-- Routed selector cursor at row entry. -/
  selector : s 36 = word w D.selector
  /-- Routed crossing cursor at row entry. -/
  crossing : s 37 = word w D.crossing

/-- Physical state reached after the first `k` ordered label candidates. -/
structure At (initial : Bank w) (mem : Memory w) (k : ℕ) (s : Bank w) (m : Memory w) : Prop where
  /-- All persistent low registers survive except the actual trial counter. -/
  low : ∀ j : Reg, j.val < 24 → j ≠ 18 → s j = initial j
  /-- Word-sized trial cursor. -/
  trial : readings s 18 = k
  /-- The singleton scan consumes no selector words. -/
  selector : s 36 = word w D.selector
  /-- Crossing consumption of exactly the preceding selected off-diagonal intervals. -/
  crossing : s 37 = word w (D.before mem k).1
  /-- Exact sequence of writes from all prior accepted families. -/
  memory : m = (D.before mem k).2

private theorem bump {initial s : Bank w} {mem m : Memory w} {k : ℕ} (one : readings s 1 = 1)
    (trial : readings s 18 = k) (cap : k+1 < 2^w) (low : ∀ j : Reg, j.val < 24 → j ≠ 18 → s j = initial j)
    (sel : s 36 = word w D.selector) (cross : s 37 = word w (D.before mem (k+1)).1)
    (hm : m = (D.before mem (k+1)).2) : D.At initial mem (k+1) (bumpBank s 18) m := by
  have fits : (s 18).val + (s 1).val < 2^w := by
    change readings s 18 + readings s 1 < _
    rwa [trial,one]
  refine ⟨fun j hj hn => (Function.update_of_ne hn ..).trans (low j hj hn),?_,sel,cross,hm⟩
  change ((Function.update s 18 (s 18 + s 1)) 18).val = k+1
  rw [Function.update_self,Fin.val_add_eq_of_add_lt fits]
  exact congrArg₂ Nat.add trial one

/-- Private bits consumed by one family: all its singleton bits on the diagonal, none across
distinct groups. -/
def localBits (t : Fin (singlePairTrials n d)) :=
  ((D.positions t).map Position.digit).flatMap Digit.choices

/-- Whole native singleton-row scan. Rejected candidates consume no private bit. Every selected
pair scatters the prescribed bits at its real mixed-radix address, advancing the shared stream
only for distinct groups. The complete bound charges the bit loop only at selected pairs. -/
theorem scatterRow_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (initial : Bank w) (m₀ : Memory w) (entry : D.Entry initial)
    (prepared : D.PreparedRow src m₀) (frameZ : (pub 0).val+56 ∈ src) (frameBank : (pub 0).val+88 ∈ src)
    (zAt : readings m₀ ((pub 0).val+56) = d^(n+1)) (bankAt : readings m₀ ((pub 0).val+88) = D.bank)
    (frameFit : (pub 0).val+88 < 2^w) (keys : d^(n+1)*d^(n+1) ≤ 2^w)
    (allocation : D.bank+d^(n+1)*d^(n+1)*len < 2^w) :
    TraceRun pub mac (rowLoop (singleCandidate n) scatterSingle) initial m₀
      (rowChoices D.selected D.localBits)
      ((∑ t : Fin (singlePairTrials n d), (6*n+17+3 + if D.selected t then startSingle.slots+5*len+2 else 1))+1)
      (D.At initial m₀ (singlePairTrials n d)) := by
  let N := singlePairTrials n d
  let I := D.At initial m₀
  let P (t : Fin N) (r : Bank w) (m : Memory w) := I t.val r m ∧
    readings r 24 = (D.codes t).1 ∧ readings r 25 = (D.codes t).2 ∧
    readings r 40 = if D.selected t then 1 else 0
  have cap : N < 2^w := by
    change singlePairTrials n d < _
    rw [← entry.bound]
    exact (initial 19).isLt
  have regs k r m (hi : I k r m) : readings r 18 = k ∧ readings r 19 = N :=
    ⟨hi.trial,(congrArg Fin.val (hi.low 19 (by decide) (by decide))).trans entry.bound⟩
  have prepare (t : Fin N) r m (hi : I t.val r m) :
      TraceRun pub mac (singleCandidate n) r m [] (6*n+17) (P t) := by
    have low (j : Reg) (hj : j.val < 24) (hn : j ≠ 18) := congrArg Fin.val (hi.low j hj hn)
    obtain ⟨fitL,fitR,_,_⟩ := D.fits t keys allocation
    obtain ⟨es,y,my,run,cost,addrL,addrR,flag,keep,unchanged⟩ := singleCandidate_run pub mac r m D.axis D.left D.right t
      ((low 0 (by decide) (by decide)).trans entry.zero) ((low 1 (by decide) (by decide)).trans entry.one)
      ((low 10 (by decide) (by decide)).trans entry.radix) ((low 11 (by decide) (by decide)).trans entry.tails)
      ((low 12 (by decide) (by decide)).trans entry.place) ((low 14 (by decide) (by decide)).trans entry.left)
      ((low 15 (by decide) (by decide)).trans entry.right) hi.trial fitL fitR
    have frame := singleCandidate_frame n
    have events := run.unsigned_events frame.1
    refine ⟨es,y,my,run,⟨rfl,List.flatMap_eq_nil_iff.mpr (fun e he => (events e he).1),
      fun e he => (events e he).2⟩,cost,?_,addrL,addrR,flag⟩
    exact ⟨fun j hj hn => (Fin.ext (keep j hj)).trans (hi.low j hj hn),(keep 18 (by decide)).trans hi.trial,
      (run.keepsReg frame.2.1).trans hi.selector,(run.keepsReg frame.2.2).trans hi.crossing,
      (funext fun j => Fin.ext (congrFun unchanged j)).trans hi.memory⟩
  have flag t r m (hp : P t r m) : r 40 = r 1 ↔ D.selected t := by
    obtain ⟨hi,_,_,flag⟩ := hp
    have unit : readings r 1 = 1 := (congrArg Fin.val (hi.low 1 (by decide) (by decide))).trans entry.one
    rw [Fin.ext_iff]
    change readings r 40 = readings r 1 ↔ _
    by_cases h : D.selected t <;> simp [flag,unit,h]
  have visit (t : Fin N) (yes : D.selected t) r m (hp : P t r m) :
      TraceRun pub mac scatterSingle r m (D.localBits t) (startSingle.slots+5*len+2)
        (fun y my => I (t.val+1) (bumpBank y 18) my) := by
    obtain ⟨hi,left,right,_⟩ := hp
    have low (j : Reg) (hj : j.val < 24) (hn : j ≠ 18) := congrArg Fin.val (hi.low j hj hn)
    have same : decide (r 14 = r 15) = decide (D.left = D.right) := by
      rw [decide_eq_decide,Fin.ext_iff,Fin.ext_iff]
      change readings r 14 = readings r 15 ↔ _
      rw [show readings r 14 = D.left.val from (low 14 (by decide) (by decide)).trans entry.left,
        show readings r 15 = D.right.val from (low 15 (by decide) (by decide)).trans entry.right]
    have width : (D.bits t).length = len := List.length_ofFn
    have source (j : ℕ) (hj : j ∈ src) : m j = m₀ j :=
      (congrFun hi.memory j).trans (D.before_source m₀ prepared t.val j hj)
    have ready := prepared_congr _ _ _ _ source (prepared t yes)
    obtain ⟨_,_,keyFit,allocFit⟩ := D.fits t keys allocation
    have destFit : singleBase D.bank (d^(n+1)) (D.bits t).length (D.codes t).1 (D.codes t).2+(D.bits t).length < 2^w := by
      simpa only [width,address] using allocFit
    have input : Prepared src (singlePositions (decide (r 14 = r 15)) (D.bits t))
        ⟨D.selector,(D.before m₀ t.val).1,singleBase D.bank (d^(n+1)) (D.bits t).length (D.codes t).1 (D.codes t).2⟩ m := by
      simpa only [same,width,positions,address] using ready
    obtain ⟨y,es,run,trace,cost,cursor,stable⟩ := scatterSingle_run pub mac src (D.bits t) D.bank (d^(n+1))
      (D.codes t).1 (D.codes t).2 D.selector (D.before m₀ t.val).1 r m left right
      ((low 21 (by decide) (by decide)).trans (entry.width.trans width.symm)) hi.selector hi.crossing
      ((congrArg Fin.val (source _ frameZ)).trans zAt) ((congrArg Fin.val (source _ frameBank)).trans bankAt)
      frameFit keyFit destFit input
    have keep (j : Reg) (hj : j.val < 24) : y j = r j :=
      stable j ((by decide : ∀ j : Reg, j.val < 24 → j ∉ ([36,37,38,55,56,57,59,60,62,63] : List Reg)) j hj)
    rw [single_advance,same,width] at cursor
    refine ⟨es,y,_,run,by simpa only [localBits,positions,same] using trace,by simpa only [width] using cost,?_⟩
    apply D.bump ((congrArg Fin.val (keep 1 (by decide))).trans ((low 1 (by decide) (by decide)).trans entry.one))
      ((congrArg Fin.val (keep 18 (by decide))).trans hi.trial) (Nat.succ_le_of_lt t.isLt |>.trans_lt cap)
      (fun j hj hn => (keep j hj).trans (hi.low j hj hn)) cursor.1
    · rw [D.before_visit m₀ t yes]
      simpa only [crossWords,decide_eq_true_eq] using cursor.2.1
    · rw [D.before_visit m₀ t yes]
      simp only [same,width,positions,address,hi.memory]
  have skip (t : Fin N) (no : ¬D.selected t) r m (hp : P t r m) : I (t.val+1) (bumpBank r 18) m := by
    have hi := hp.1
    apply D.bump ((congrArg Fin.val (hi.low 1 (by decide) (by decide))).trans entry.one) hi.trial
      (Nat.succ_le_of_lt t.isLt |>.trans_lt cap) hi.low hi.selector
    · simpa only [D.before_skip m₀ t no] using hi.crossing
    · simpa only [D.before_skip m₀ t no] using hi.memory
  exact traceRow_run (singleCandidate n) scatterSingle (6*n+17) D.selected D.localBits
    (fun _ => startSingle.slots+5*len+2) I P regs prepare flag visit skip initial m₀
    ⟨fun _ _ _ => rfl,entry.start,entry.selector,entry.crossing,rfl⟩

end Cube.Scatter.SingleRowData

end BorderVNP
end Computability
end OAI
