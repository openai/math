import OAI.ThreeFlat.Diagonal.TraceIterationLimits
import OAI.ThreeFlat.Diagonal.NavigationRecordedArrayBounds
import OAI.ThreeFlat.Diagonal.TraceStageConstants
import OAI.Hierarchy.TraceShrinkArchivePass
import OAI.Hierarchy.TraceRefreshArchivePass
import OAI.ThreeFlat.Diagonal.NavigationArchiveVisit
import OAI.ThreeFlat.Diagonal.NavigationQuotaImage
import OAI.ThreeFlat.Diagonal.PhysicalProgramRecords

namespace OAI
/-! # Site and wire reconstruction along a width-parametric native chronology

An entry records the actual stored source graph and native move result, the unique parsed
histogram, and the next directory cursor. Except at loop back-edges, adjacent entries share
their physical memory; each back-edge writes only the independent block counter.
-/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure PhysicalStage
open CompressorPacking Native NavigationDirectory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

/-- The numerical preconditions of every local native call, derived from a single trim
of the actual full navigation directory into past, current and future stages. -/
theorem Archive.TraceLimits.at_step {W : ℕ} {a : Archive} {limit edges cap : ℕ} {cur : Word W}
    {pre post : List Stage} {step : Stage} (all : a.TraceLimits limit cur (pre++step::post) edges cap) :
    let c:=finish a.K pre a.cursor
    let steps:=pre++step::post
    a.cursor.dense+a.histWords steps≤c.heap ∧ c.header+64≤a.cursor.dense ∧
      (allocate a.K c step).next.heap≤cur.val ∧ step.heapWords≤limit ∧
      W*(a.K*(pre.map Stage.motifs).sum)+step.motifs*a.K*W≤cap := by
  intro c steps
  have before : a.cursor.heap≤c.heap := by dsimp only [c];rw [heap_finish];omega
  have dense:=all.raw
  have static:=all.tables
  have ctl:=all.controls
  have total:=all.volume
  have capacity:=all.capacity
  rw [Archive.directory_length,List.length_append,List.length_cons,Nat.mul_add] at static
  rw [show c.header=a.cursor.header+64*pre.length from header_finish ..,all.origin]
  simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons] at ctl total
  have bound : (allocate a.K c step).next.heap≤cur.val := by
    rw [heap_step,show c.heap=a.cursor.heap+(pre.map Stage.heapWords).sum from heap_finish ..]
    omega
  have cells : a.K*(pre.map Stage.motifs).sum+step.motifs*a.K≤a.histWords steps := by
    dsimp only [steps,Archive.histWords]
    simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons,Nat.mul_add]
    rw [Nat.mul_comm step.motifs]
    omega
  have bytes := (Nat.mul_le_mul_left W cells).trans capacity
  rw [Nat.mul_add,Nat.mul_comm W (step.motifs*a.K)] at bytes
  exact ⟨dense.trans before,by omega,bound,by omega,bytes⟩


open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink

/-- A loop-back changes only the counted ROM's repetition register in external memory. -/
def traceExceptCounter {W : ℕ} (ctr : Word W) (m m' : Memory W) : Prop :=
  ∀ addr,addr≠ctr.val → m' addr=m addr

structure TraceMoveRoom {W : ℕ} (limit K : ℕ) (cur : Word W) (c : Cursor) (op : Stage)
    (maxWidth fixedWords : ℕ) : Prop where
  fixed : fixedWords≤limit
  volume : op.heapWords≤limit
  wire : maxWidth+1≤(limit)^4
  width : 0<c.width
  heap : (allocate K c op).next.heap≤cur.val

/-- The exact native post for every selected chronological row, with its original source
memory, actual histogram choice and persistent writes. The program index fixes the
complete dependent graph and degree at every stage, including the refresh reindexing. -/
def Archive.TraceJournal {W : ℕ} (a : Archive) (limit : ℕ) (cur ctr : Word W) :
    {s : ℕ} → (P : Program F s) → (rem : ℕ) → State (2^s) (P.charge+rem) → Cursor →
      List Bool → Memory W → Memory W → Prop
  | _,.done _,_,_,_,_,input,final => traceExceptCounter ctr input final
  | _,.shrink s t G small tail,rem,X,c,raw,input,final =>
    let b:=tail.charge+rem
    let B : State (2^s) (shrinkCharge s+b):=(Nat.add_assoc (shrinkCharge s) tail.charge rem) ▸ X
    let ok : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/(2^t:ℕ)≤1/1024 := by exact_mod_cast small
    let M:=shrinkBinary G s (2^t) b (Nat.two_pow_pos _) ok B
    let Q:=shrinkBinaryFamily G s (2^t) b (Nat.two_pow_pos _) ok B
    let x:=dims (shrinkStage s (2^t)) (Fintype.card (shrinkRecordState s b B).Base) (CompressorPacking.tagBits (2^s)) b
    ∃ (m out : Memory W) (fit : Q.Fits a.K W) (j : Fin M.rules.count),
      traceExceptCounter ctr input m ∧ (Q.record fit).read (raw.take (Q.record fit).width)=some j ∧
      (Program.shrink s t G small tail).directory rem (Fintype.card X.Base)=
        .shrink x::tail.directory rem (Fintype.card (M.next j).Base) ∧
      TraceMoveRoom limit a.K cur c (.shrink x) B.maxWidth (Hierarchy.TraceShrinkRetained.fixedWords G s (2^t)) ∧
      (OldArrayBounds a.cursor.dense c B ∧ SlotImage.Stored B.graph B.order (tagOrdinal _)
        (RefreshStageNav.oldColumns c (@Fintype.card B.Base B.finiteBase) (2^s)) (fun i=>(m i).val) B.width) ∧
      ShrinkOutput (K:=a.K) G s (2^t) b (Nat.two_pow_pos _) ok B cur m c j out ∧
      a.TraceJournal limit cur ctr tail rem (M.next j) (allocate a.K c (.shrink x)).next
        (raw.drop (Q.record fit).width) out final
  | _,.refresh s t h pad g γ C G hm hh sym rows zero conn deg tail,rem,X,c,raw,input,final =>
    let b:=tail.charge+rem
    let B : State (2^s) (s+b):=(Nat.add_assoc s tail.charge rem) ▸ X
    let R:=refreshBinary G B hm hh sym rows zero conn
    let M:=Program.recastMove deg R
    let Q:=refreshBinaryFamily G B hm hh sym rows zero conn
    let en:=allocate a.K c (.refresh (@Fintype.card B.Base B.finiteBase) (2^s) (2^b) h pad)
    ∃ (m out : Memory W) (fit : Q.Fits a.K W) (j : Fin R.rules.count),
      let middle:=((refreshPre G cur).pipeline cur).run m
      traceExceptCounter ctr input m ∧ (Q.record fit).read (raw.take (Q.record fit).width)=some j ∧
      (Program.refresh s t h pad g γ C G hm hh sym rows zero conn deg tail).directory rem (Fintype.card X.Base)=
        .refresh (@Fintype.card B.Base B.finiteBase) (2^s) (2^b) h pad::tail.directory rem (Fintype.card (M.next (Program.degreeTerm deg R j)).Base) ∧
      TraceMoveRoom limit a.K cur c (.refresh (@Fintype.card B.Base B.finiteBase) (2^s) (2^b) h pad) B.maxWidth (refreshFixedWords G) ∧
      (OldArrayBounds a.cursor.dense c B ∧ SlotImage.Stored B.graph B.order (tagOrdinal _)
        (RefreshStageNav.oldColumns c (@Fintype.card B.Base B.finiteBase) (2^s)) (fun i=>(m i).val) B.width) ∧
      RefreshOutput G B hm hh sym rows zero conn a.K cur c j middle out ∧
      ((∀ (i : Fin Q.motifs) (f : Fin 3),out (c.heap+(i.val*3+f.val))=
        ((if f.val=0 then Q.copies i else if f.val=1 then
          (G.winner (refreshBinaryGraph B) (tagOrdinal s).symm (refreshBinaryInput B)
            ((refreshBlockOrder B).symm i)).val else Fintype.card (Q.alphabet i):ℕ):Word W)) ∧
        QuotaImage Q fit j c out ∧ c.header+64*(tail.length+1)≤c.dense) ∧
      (∀ k,k≠cur.val → (k<c.heap ∨ en.next.heap≤k) → out k=m k) ∧
      a.TraceJournal limit cur ctr tail rem (M.next (Program.degreeTerm deg R j)) en.next
        (raw.drop (Q.record fit).width) out final

theorem traceExceptCounter.trans {W : ℕ} {ctr : Word W} {m n o : Memory W}
    (left : traceExceptCounter ctr m n) (right : traceExceptCounter ctr n o) : traceExceptCounter ctr m o :=
  fun i hi=>(right i hi).trans (left i hi)

/-- The physical counter write on a loop-back preserves the typed run just recorded. -/
theorem Archive.traceJournal_start {W : ℕ} {a : Archive} {limit s : ℕ} {cur ctr : Word W} (P : Program F s)
    (rem : ℕ) (X : State (2^s) (P.charge+rem)) (c : Cursor) (raw : List Bool)
    {m n final : Memory W} (frame : traceExceptCounter ctr m n) :
    a.TraceJournal limit cur ctr P rem X c raw n final → a.TraceJournal limit cur ctr P rem X c raw m final := by
  cases P with
  | done s => exact fun h=>frame.trans h
  | shrink s t G small tail =>
    rintro ⟨first,out,fit,j,boot,h⟩
    exact ⟨first,out,fit,j,frame.trans boot,h⟩
  | refresh s t h pad g γ C G hm hh sym rows zero conn degree tail =>
    rintro ⟨first,out,fit,j,boot,rest⟩
    exact ⟨first,out,fit,j,frame.trans boot,rest⟩

/-- An address disjoint from the stage-selector header interval and the write-once
output heap for the remaining run. Both S38 and S49 may lie above the finished heap. -/
def traceOutsideWrites (K : ℕ) (c : Cursor) (rows : List Stage) (addr : ℕ) : Prop :=
  (addr<c.header ∨ (finish K rows c).header≤addr) ∧
  (addr<c.heap ∨ (finish K rows c).heap≤addr)

private theorem traceOutside_cons {K addr : ℕ} {c : Cursor} {s : Stage} {rest : List Stage}
    (h : traceOutsideWrites K c (s::rest) addr) :
    let next:=(allocate K c s).next
    addr≠c.header+27 ∧ (addr<c.heap ∨ next.heap≤addr) ∧ traceOutsideWrites K next rest addr := by
  intro next
  have head : next.header=c.header+64 := by cases s <;> rfl
  have heap : next.heap=c.heap+s.heapWords:=heap_step ..
  change (addr<c.header ∨ (finish K rest next).header≤addr) ∧
    (addr<c.heap ∨ (finish K rest next).heap≤addr) at h
  obtain ⟨hh,ha⟩:=h
  rw [header_finish] at hh
  rw [heap_finish] at ha
  dsimp [traceOutsideWrites]
  rw [header_finish,heap_finish]
  omega

/-- A fully executed adaptive journal preserves every protected input word, even when
the deciding histograms select different intermediate numbers and widths of wires. -/
theorem Archive.TraceJournal.frame {W : ℕ} {a : Archive} {limit s : ℕ} {cur ctr : Word W} (P : Program F s)
    (rem : ℕ) (X : State (2^s) (P.charge+rem)) (c : Cursor) (raw : List Bool)
    {m final : Memory W} (journal : a.TraceJournal limit cur ctr P rem X c raw m final)
    {addr : ℕ} (hc : addr≠cur.val) (ht : addr≠ctr.val)
    (apart : traceOutsideWrites a.K c (P.directory rem (Fintype.card X.Base)) addr) : final addr=m addr := by
  induction P generalizing rem c raw m final with
  | done s => exact journal addr ht
  | shrink s t G small tail ih =>
    rcases journal with ⟨mid,out,fit,j,origin,read,shape,room,oldGraph,records,cont⟩
    rw [shape] at apart
    obtain ⟨hdr,span,rest⟩:=traceOutside_cons apart
    exact (ih _ _ _ _ cont rest).trans ((records.archive addr hc hdr span).trans (origin addr ht))
  | refresh s t h pad g γ C G hm hh sym rows zero conn deg tail ih =>
    rcases journal with ⟨mid,out,fit,j,origin,read,shape,room,oldGraph,records,published,frame,cont⟩
    rw [shape] at apart
    obtain ⟨hdr,span,rest⟩:=traceOutside_cons apart
    exact (ih _ _ _ _ cont rest).trans ((frame addr hc span).trans (origin addr ht))



end
end ThreeFlat.Diagonal.NavigationPass

end OAI
