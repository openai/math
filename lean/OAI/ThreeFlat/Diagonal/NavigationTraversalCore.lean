import OAI.ThreeFlat.Diagonal.NavigationRecordedWordStep
import OAI.ThreeFlat.Diagonal.PhysicalRunRootNumber
import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.Diagonal.NavigationCounted
import OAI.ThreeFlat.Diagonal.PhysicalNativeTime
import OAI.ThreeFlat.Diagonal.TickWorkspace

import OAI.ThreeFlat.Diagonal.PhysicalNodeArchivePath
import OAI.ThreeFlat.Diagonal.ShrinkChildAssemblyOrder
import OAI.ThreeFlat.Diagonal.PhysicalProgramAssembly

namespace OAI
/-! # Reading the true adaptive tensor history along the installed chronological row loop -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure PhysicalStage
open CompressorPacking Native NavigationDirectory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

/-- The fixed, age-independent width threshold of any row in a finite physical program. -/
def wordConstants : {s : ℕ} → Program F s → List ℕ
  | _,.done _=>[]
  | _,.shrink s t T _ tail=>shrinkFixedWords T s (2^t)::wordConstants tail
  | _,.refresh _ _ _ _ _ _ _ T _ _ _ _ _ _ _ tail=>refreshFixedWords T::wordConstants tail

open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink

/-- A loop-back changes only the counted ROM's repetition register in external memory. -/
def exceptCounter {W : ℕ} (ctr : Word W) (m m' : Memory W) : Prop :=
  ∀ addr,addr≠ctr.val → m' addr=m addr

structure MoveRoom (u K : ℕ) (cur : Word (16*u^10)) (c : Cursor) (op : Stage)
    (maxWidth fixedWords : ℕ) : Prop where
  fixed : fixedWords≤u
  volume : op.heapWords≤2^(u^10)
  wire : maxWidth+1≤(2^(u^10))^4
  width : 0<c.width
  heap : (allocate K c op).next.heap≤cur.val

/-- The exact native post for every selected chronological row, with its original source
memory, actual histogram choice and persistent writes. The program index fixes the
complete dependent graph and degree at every stage, including the refresh reindexing. -/
def Archive.Journal (a : Archive) (u : ℕ) (cur ctr : Word (16*u^10)) :
    {s : ℕ} → (P : Program F s) → (rem : ℕ) → State (2^s) (P.charge+rem) → Cursor →
      List Bool → Memory (16*u^10) → Memory (16*u^10) → Prop
  | _,.done _,_,_,_,_,input,final => exceptCounter ctr input final
  | _,.shrink s t G small tail,rem,X,c,raw,input,final =>
    let b:=tail.charge+rem
    let B : State (2^s) (shrinkCharge s+b):=(Nat.add_assoc (shrinkCharge s) tail.charge rem) ▸ X
    let ok : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/(2^t:ℕ)≤1/1024 := by exact_mod_cast small
    let M:=shrinkBinary G s (2^t) b (Nat.two_pow_pos _) ok B
    let Q:=shrinkBinaryFamily G s (2^t) b (Nat.two_pow_pos _) ok B
    let x:=dims (shrinkStage s (2^t)) (Fintype.card (shrinkRecordState s b B).Base) (CompressorPacking.tagBits (2^s)) b
    ∃ (m out : Memory (16*u^10)) (fit : Q.Fits a.K (16*u^10)) (j : Fin M.rules.count),
      exceptCounter ctr input m ∧ (Q.record fit).read (raw.take (Q.record fit).width)=some j ∧
      (Program.shrink s t G small tail).directory rem (Fintype.card X.Base)=
        .shrink x::tail.directory rem (Fintype.card (M.next j).Base) ∧
      MoveRoom u a.K cur c (.shrink x) B.maxWidth (shrinkFixedWords G s (2^t)) ∧
      (OldArrayBounds a.cursor.dense c B ∧ SlotImage.Stored B.graph B.order (tagOrdinal _)
        (RefreshStageNav.oldColumns c (@Fintype.card B.Base B.finiteBase) (2^s)) (fun i=>(m i).val) B.width) ∧
      ShrinkOutput (K:=a.K) G s (2^t) b (Nat.two_pow_pos _) ok B cur m c j out ∧
      a.Journal u cur ctr tail rem (M.next j) (allocate a.K c (.shrink x)).next
        (raw.drop (Q.record fit).width) out final
  | _,.refresh s t h pad g γ C G hm hh sym rows zero conn deg tail,rem,X,c,raw,input,final =>
    let b:=tail.charge+rem
    let B : State (2^s) (s+b):=(Nat.add_assoc s tail.charge rem) ▸ X
    let R:=refreshBinary G B hm hh sym rows zero conn
    let M:=Program.recastMove deg R
    let Q:=refreshBinaryFamily G B hm hh sym rows zero conn
    let en:=allocate a.K c (.refresh (@Fintype.card B.Base B.finiteBase) (2^s) (2^b) h pad)
    ∃ (m out : Memory (16*u^10)) (fit : Q.Fits a.K (16*u^10)) (j : Fin R.rules.count),
      let middle:=((refreshPre G cur).pipeline cur).run m
      exceptCounter ctr input m ∧ (Q.record fit).read (raw.take (Q.record fit).width)=some j ∧
      (Program.refresh s t h pad g γ C G hm hh sym rows zero conn deg tail).directory rem (Fintype.card X.Base)=
        .refresh (@Fintype.card B.Base B.finiteBase) (2^s) (2^b) h pad::tail.directory rem (Fintype.card (M.next (Program.degreeTerm deg R j)).Base) ∧
      MoveRoom u a.K cur c (.refresh (@Fintype.card B.Base B.finiteBase) (2^s) (2^b) h pad) B.maxWidth (refreshFixedWords G) ∧
      (OldArrayBounds a.cursor.dense c B ∧ SlotImage.Stored B.graph B.order (tagOrdinal _)
        (RefreshStageNav.oldColumns c (@Fintype.card B.Base B.finiteBase) (2^s)) (fun i=>(m i).val) B.width) ∧
      RefreshOutput G B hm hh sym rows zero conn a.K cur c j middle out ∧
      ((∀ (i : Fin Q.motifs) (f : Fin 3),out (c.heap+(i.val*3+f.val))=
        ((if f.val=0 then Q.copies i else if f.val=1 then
          (G.winner (refreshBinaryGraph B) (tagOrdinal s).symm (refreshBinaryInput B)
            ((refreshBlockOrder B).symm i)).val else Fintype.card (Q.alphabet i):ℕ):Word (16*u^10))) ∧
        QuotaImage Q fit j c out ∧ c.header+64*(tail.length+1)≤c.dense) ∧
      (∀ k,k≠cur.val → (k<c.heap ∨ en.next.heap≤k) → out k=m k) ∧
      a.Journal u cur ctr tail rem (M.next (Program.degreeTerm deg R j)) en.next
        (raw.drop (Q.record fit).width) out final

theorem exceptCounter.trans {W : ℕ} {ctr : Word W} {m n o : Memory W}
    (left : exceptCounter ctr m n) (right : exceptCounter ctr n o) : exceptCounter ctr m o :=
  fun i hi=>(right i hi).trans (left i hi)

/-- The physical counter write on a loop-back preserves the typed run just recorded. -/
theorem Archive.journal_start {a : Archive} {u s : ℕ} {cur ctr : Word (16*u^10)} (P : Program F s)
    (rem : ℕ) (X : State (2^s) (P.charge+rem)) (c : Cursor) (raw : List Bool)
    {m n final : Memory (16*u^10)} (frame : exceptCounter ctr m n) :
    a.Journal u cur ctr P rem X c raw n final → a.Journal u cur ctr P rem X c raw m final := by
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
def outsideWrites (K : ℕ) (c : Cursor) (rows : List Stage) (addr : ℕ) : Prop :=
  (addr<c.header ∨ (finish K rows c).header≤addr) ∧
  (addr<c.heap ∨ (finish K rows c).heap≤addr)

private theorem outside_cons {K addr : ℕ} {c : Cursor} {s : Stage} {rest : List Stage}
    (h : outsideWrites K c (s::rest) addr) :
    let next:=(allocate K c s).next
    addr≠c.header+27 ∧ (addr<c.heap ∨ next.heap≤addr) ∧ outsideWrites K next rest addr := by
  intro next
  have head : next.header=c.header+64 := by cases s <;> rfl
  have heap : next.heap=c.heap+s.heapWords:=heap_step ..
  change (addr<c.header ∨ (finish K rest next).header≤addr) ∧
    (addr<c.heap ∨ (finish K rest next).heap≤addr) at h
  obtain ⟨hh,ha⟩:=h
  rw [header_finish] at hh
  rw [heap_finish] at ha
  dsimp [outsideWrites]
  rw [header_finish,heap_finish]
  omega

/-- A fully executed adaptive journal preserves every protected input word, even when
the deciding histograms select different intermediate numbers and widths of wires. -/
theorem Archive.Journal.frame {a : Archive} {u s : ℕ} {cur ctr : Word (16*u^10)} (P : Program F s)
    (rem : ℕ) (X : State (2^s) (P.charge+rem)) (c : Cursor) (raw : List Bool)
    {m final : Memory (16*u^10)} (journal : a.Journal u cur ctr P rem X c raw m final)
    {addr : ℕ} (hc : addr≠cur.val) (ht : addr≠ctr.val)
    (apart : outsideWrites a.K c (P.directory rem (Fintype.card X.Base)) addr) : final addr=m addr := by
  induction P generalizing rem c raw m final with
  | done s => exact journal addr ht
  | shrink s t G small tail ih =>
    rcases journal with ⟨mid,out,fit,j,origin,read,shape,room,oldGraph,records,cont⟩
    rw [shape] at apart
    obtain ⟨hdr,span,rest⟩:=outside_cons apart
    exact (ih _ _ _ _ cont rest).trans ((records.archive addr hc hdr span).trans (origin addr ht))
  | refresh s t h pad g γ C G hm hh sym rows zero conn deg tail ih =>
    rcases journal with ⟨mid,out,fit,j,origin,read,shape,room,oldGraph,records,published,frame,cont⟩
    rw [shape] at apart
    obtain ⟨hdr,span,rest⟩:=outside_cons apart
    exact (ih _ _ _ _ cont rest).trans ((frame addr hc span).trans (origin addr ht))

structure Traversal (F : Type) [Field F] (u : ℕ) where
  archive : Archive
  field : FieldCode F (16*u^10)
  current : Word (16*u^10)
  counter : Word (16*u^10)
  stages : List Stage
  procedures : List (Procedure (16*u^10))
  edges : ℕ
  capacity : ℕ
  bits : ℕ→Bool
  clock : ℕ
  prefixOK : ℕ→Prop
  journal : Memory (16*u^10)→Prop
  outcome : Run.WireLayer→List Bool→Prop
  limits : archive.Limits u current stages edges capacity
  age : 40≤u
  alphabet : archive.K≤u
  counterHigh : current.val<counter.val

namespace Traversal
variable {u : ℕ} (T : Traversal F u)
local notation "W" => (16*u^10)
local notation "a" => T.archive

/-- After i accepted actual rows, retain the real remaining typed graph and program, plus
the original input suffix and the precise position of the next native instruction. -/
structure Point (i : ℕ) (m : Memory W) where
  s : ℕ
  rem : ℕ
  program : Program F s
  state : State (2^s) (program.charge+rem)
  ceiling : ℕ
  reach : (program.run rem state).WidthCeiling ceiling
  fits : ∀ b∈program.recordBounds,b.1≤(a).K ∧ b.2*ceiling<2^W
  small : ceiling≤(2^(u^10))^4
  fixed : ∀ b∈wordConstants program,b≤u
  past : List Stage
  index : past.length=i
  directory : T.stages=past++program.directory rem (Fintype.card state.Base)
  text : T.procedures.drop i=nativeRows T.current (a).K program
  visit : (a).Visit T.stages T.edges T.bits T.current past state m
  time : Program.nativeTicks (a).K T.current program (finish (a).K past (a).cursor) rem (Fintype.card state.Base)≤T.clock
  parses : let E:=program.table (a).K W ceiling fits rem state reach
    let bits:=(List.ofFn (fun i : Fin T.capacity=>T.bits i.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
    ∀ n,T.prefixOK (i+n) ↔ Run.PrefixOK n (program.run rem state) E.records bits
  complete : let raw:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
    ∀ final,(a).Journal u T.current T.counter program rem state (finish (a).K past (a).cursor) raw m final → T.journal final
  outcome : let E:=program.table (a).K W ceiling fits rem state reach
    let bits:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
    ∀ v rest,T.outcome v rest ↔ (program.run rem state).EndsAt E.records bits v rest


theorem Point.seen {i : ℕ} {m : Memory W} (here : T.Point i m) : T.prefixOK i :=
  (here.parses 0).mpr trivial

/-- A physical decrement of the separate external loop counter preserves all cells of the
current archive. This includes old graph and edge-width words used by the next pass. -/
def Point.decrement {i : ℕ} {m : Memory W} (here : T.Point i m) (val : Word W) :
    T.Point i (writeMemory m T.counter val) := by
  let c:=finish (a).K here.past (a).cursor
  have cap : c.heap≤T.current.val := by
    have h:=T.limits.controls
    rw [here.directory,List.map_append,List.sum_append] at h
    dsimp [c];rw [heap_finish];omega
  have low : (a).cursor.dense+(a).histWords T.stages≤c.heap := by
    exact T.limits.raw.trans (by dsimp only [c];rw [heap_finish];omega)
  have static : (a).seed+((a).directory T.stages T.edges W).length≤c.heap := T.limits.tables.trans (by omega)
  have fr (j : ℕ) (hj : j<T.counter.val) : writeMemory m T.counter val j=m j := by simp [writeMemory,ne_of_lt hj]
  let visit:=here.visit
  have cn:=T.counterHigh
  have live : (a).Live T.stages T.edges T.bits T.current c (writeMemory m T.counter val) := by
    refine ⟨by rw [fr _ cn];exact visit.live.pointer,?_,?_⟩
    · intro j v beyond get
      have hj : j<((a).directory T.stages T.edges W).length := by
        by_contra! bad
        simp [List.getElem?_eq_none bad] at get
      rw [fr _ (by omega)]
      exact visit.live.headers j v beyond get
    · intro j hj
      change j<(a).histWords T.stages at hj
      rw [fr _ (by omega)]
      exact visit.live.counts _ hj
  have graphTop:=visit.graphBound
  have widthTop:=visit.widthBound
  change c.graph+6*(Fintype.card here.state.Base*2^here.s)≤c.heap at graphTop
  change c.width+here.state.edgeCount≤c.heap at widthTop
  refine {here with complete:=fun final tail=>here.complete final (Archive.journal_start _ _ _ _ _ (fun j hj=>by simp [writeMemory,hj]) tail), visit:=
    ⟨live,visit.graphLow,visit.widthLow,visit.graphBound,visit.widthBound,visit.stored.frame ?_ ?_⟩}
  · intro j _ hj
    change j<c.graph+6*(Fintype.card here.state.Base*2^here.s) at hj
    exact congrArg Fin.val (fr _ (by omega))
  · intro j _ hj
    change j<c.width+here.state.edgeCount at hj
    exact congrArg Fin.val (fr _ (by omega))


/-- Chopping one actual packed record off the binary input advances its numeric
directory cursor by precisely as many W-bit counters as the row has symbols. -/
theorem drop_record (pre : List Stage) (step : Stage) {n : ℕ} (Q : RecordFamily n)
    (fit : Q.Fits (a).K W) (same : Q.motifs=step.motifs) :
    let full:=List.ofFn (fun i : Fin T.capacity=>T.bits i.val)
    (full.drop (W*((a).K*(pre.map Stage.motifs).sum))).drop (Q.record fit).width =
      full.drop (W*((a).K*((pre++[step]).map Stage.motifs).sum)) := by
  intro full
  rw [List.drop_drop,RecordFamily.record_width,same]
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,
    Nat.mul_add]
  congr 1; ring

theorem row_after {i : ℕ} (tail : List (Procedure W)) (row : Procedure W)
    (current : T.procedures.drop i=row::tail) :
    T.procedures[i]?=some row ∧ T.procedures.drop (i+1)=tail := by
  constructor
  · have lookup := List.getElem?_drop (xs := T.procedures) (i := i) (j := 0)
    rw [current] at lookup
    exact lookup.symm
  · simpa only [List.drop_drop,Nat.add_comm 1 i,List.drop_succ_cons,List.drop_zero] using
      congrArg (List.drop 1) current

/-- Once a real current record is known, the accepted-prefix assertion at every subsequent
stop reduces to exactly the same assertion for the remaining true run. -/
theorem next_parses {i n d l D L : ℕ} {A : State d l} (R : Move F A D L) (later : ∀ j,Run F (R.next j))
    (E : (Run.step R later).Records) (bits : List Bool)
    (whole : ∀ n,T.prefixOK (i+n) ↔ Run.PrefixOK n (.step R later) E bits)
    (j : Fin R.rules.count) (record : E.1.read (bits.take E.1.width)=some j) :
    T.prefixOK ((i+1)+n) ↔ Run.PrefixOK n (later j) (E.2 j) (bits.drop E.1.width) := by
  rw [show (i+1)+n=i+(n+1) by omega,whole]
  change (∃ h,E.1.read (bits.take E.1.width)=some h ∧ _) ↔ _
  simp [record]

/-- Transport the remaining stage count and records across the input-lane reassociation,
exactly as in the physical program's original canonical table. -/
theorem input_prefix {d l l' : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) {sizes : List ℕ}
    (q : Program.RecordTable r (a).K W sizes) (bits : List Bool) (good : ℕ→Prop)
    (old : ∀ n,good n ↔ Run.PrefixOK n (Program.recast e A r)
      (Program.changeTable e A r q).records bits) :
    ∀ n,good n ↔ Run.PrefixOK n r q.records bits :=
  fun n=>(old n).trans (Program.prefix_changeTable e A r q bits)

theorem past_next (pre : List Stage) (step : Stage) :
    finish (a).K (pre++[step]) (a).cursor=(allocate (a).K (finish (a).K pre (a).cursor) step).next := by
  rw [finish_append]
  rfl

/-- Reopen the physical output slot columns as the next typed visit. The two numeric
sizes are fixed by the current stage's true old base count, for each possible branch. -/
theorem next_visit (pre : List Stage) (step : Stage) {d l : ℕ} (X : State d l) (out : Memory W)
    (rows : (match step with
      | .shrink x=>x.newEdges
      | .refresh v m k h pad=>(RefreshStageLayout.counts v m k h pad).newGraphRows)=Fintype.card X.Base*d)
    (wires : (match step with
      | .shrink x=>x.newEdges*x.residual
      | .refresh v m k h pad=>(RefreshStageLayout.counts v m k h pad).newWidthSpan)=X.edgeCount) :
    let c:=finish (a).K pre (a).cursor
    let ne:=(allocate (a).K c step).next
    (a).Live T.stages T.edges T.bits T.current ne out →
    SlotImage.Stored X.graph X.order (tagOrdinal _) (RefreshStageNav.oldColumns ne (Fintype.card X.Base) d)
      (fun k=>(out k).val) X.width →
    (a).Visit T.stages T.edges T.bits T.current (pre++[step]) X out := by
  intro c ne live stored
  have low : (a).cursor.dense≤c.heap := by
    have h:=T.limits.raw
    dsimp only [c];rw [heap_finish];omega
  obtain ⟨lowGraph,lowWidth,graphBound,widthBound⟩:=successor_resident (a).K c step
  have graphRoom : ne.graph+6*(Fintype.card X.Base*d) ≤ ne.heap := by
    cases step <;> rw [←rows] <;> exact graphBound
  have widthRoom : ne.width+X.edgeCount ≤ ne.heap := by
    cases step <;> rw [←wires] <;> exact widthBound
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> rw [T.past_next]
  · exact live
  · exact low.trans lowGraph
  · exact low.trans lowWidth
  · exact graphRoom
  · exact widthRoom
  · exact stored

theorem first_record {i d l D L : ℕ} {A : State d l} (R : Move F A D L) (later : ∀ j,Run F (R.next j))
    (E : (Run.step R later).Records) (raw : List Bool)
    (whole : ∀ n,T.prefixOK (i+n) ↔ Run.PrefixOK n (.step R later) E raw) :
    T.prefixOK (i+1) ↔ (E.1.read (raw.take E.1.width)).isSome := by
  rw [whole]
  change (∃ j,E.1.read (raw.take E.1.width)=some j ∧ True) ↔ _
  simp [Option.isSome_iff_exists]

section Shrink
open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink

variable {s t i : ℕ} {G : ShrinkMotif.Table F}
    {small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/2^t≤1/1024} (tail : Program F t)
local notation "P" => Program.shrink s t G small tail

private theorem directory_tail_eq {α : Type*} (seen stages current future : List α) (op : α)
    (before : stages=seen++current) (after : stages=(seen++[op])++future) : current=op::future := by
  have both := before.symm.trans after
  rw [List.append_assoc] at both
  exact List.append_cancel_left both

set_option maxHeartbeats 2400000 in
/-- Execute a shrinking row of the physical loop, preserving all prefix assertions
at every future stop on the unique chosen successor. -/
theorem shrink_point (rem Z : ℕ) (X : State (2^s) ((P).charge+rem)) (m : Memory W)
    (reach : ((P).run rem X).WidthCeiling Z) (bounds : ∀ b∈(P).recordBounds,b.1≤(a).K ∧ b.2*Z<2^W)
    (smallZ : Z≤(2^(u^10))^4) (fixed : ∀ b∈wordConstants P,b≤u)
    (past : List Stage) (idx : past.length=i) (dir : T.stages=past++(P).directory rem (Fintype.card X.Base))
    (text : T.procedures.drop i=nativeRows T.current (a).K P) (vis : (a).Visit T.stages T.edges T.bits T.current past X m)
    (time : Program.nativeTicks (a).K T.current P (finish (a).K past (a).cursor) rem (Fintype.card X.Base)≤T.clock)
    (reads : let q:=(P).table (a).K W Z bounds rem X reach
      let raw:=(List.ofFn (fun i : Fin T.capacity=>T.bits i.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ n,T.prefixOK (i+n) ↔ Run.PrefixOK n ((P).run rem X) q.records raw)
    (complete : let raw:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ final,(a).Journal u T.current T.counter P rem X (finish (a).K past (a).cursor) raw m final → T.journal final)
    (ends : let q:=(P).table (a).K W Z bounds rem X reach
      let raw:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ v rest,T.outcome v rest ↔ ((P).run rem X).EndsAt q.records raw v rest) :
    let row:=shrink T.current (a).K s (2^t) G
    TickStageSpec.Admission T.field row.block row.publicData (fun x=>x=m) (fun _=>T.prefixOK (i+1))
      (fun _ out=>Nonempty (T.Point (i+1) out) ∧ out T.counter.val=m T.counter.val) T.clock := by
  intro row
  let b:=tail.charge+rem
  let eqv:=Nat.add_assoc (shrinkCharge s) tail.charge rem
  let B : State (2^s) (shrinkCharge s+b):=eqv ▸ X
  let ok : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/(2^t:ℕ)≤1/1024:=by exact_mod_cast small
  let M:=shrinkBinary G s (2^t) b (Nat.two_pow_pos _) ok B
  let next:=fun j=>tail.run rem (M.next j)
  let Q:=shrinkBinaryFamily G s (2^t) b (Nat.two_pow_pos _) ok B
  let dims₀:=dims (shrinkStage s (2^t)) (Fintype.card (shrinkRecordState s b B).Base) (CompressorPacking.tagBits (2^s)) b
  let op:=Stage.shrink dims₀
  let rest:=tail.directory rem ((@Fintype.card B.Base B.finiteBase)*2^(CompressorPacking.tagBits (2^s)))
  let csr:=finish (a).K past (a).cursor
  let raw:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
  have bv : Fintype.card B.Base=Fintype.card X.Base:=Program.baseCast eqv X
  have nb:=shrink_record_base s b B
  have dir' : T.stages=past++op::rest := by
    dsimp only [op,dims₀,rest];rw [nb,bv];exact dir
  have limits:=T.limits
  rw [dir'] at limits
  obtain ⟨dense,later,control,volume,cap⟩:=limits.at_step
  have vc:=vis.cast eqv
  change (a).Visit T.stages T.edges T.bits T.current past B m at vc
  rw [dir'] at vc
  have ce : (Run.step M next).WidthCeiling Z:=Program.beforeRecast eqv X _ reach
  have hb:=bounds _ List.mem_cons_self
  have fit : Q.Fits (a).K W:=shrinkBinaryFamily_fits G s (2^t) _ _ _ B hb.1
    ((Nat.mul_le_mul_left _ (by simpa [Nat.add_comm] using ce.1)).trans_lt hb.2)
  let laterBounds : ∀ b∈tail.recordBounds,b.1≤(a).K ∧ b.2*Z<2^W:=fun b h=>bounds b (List.mem_cons_of_mem _ h)
  let qt:=fun j=>tail.table (a).K W Z laterBounds rem (M.next j) (ce.2 j)
  let E : (Run.step M next).Records := ((Q.record fit),fun j=>(qt j).records)
  let stepTable : Program.RecordTable (.step M next) T.archive.K W
      (((P).directory rem (Fintype.card X.Base)).map Stage.motifs) := by
    apply Program.consTable M next Q fit
    · dsimp only [Q]
      rw [shrinkBinaryFamily_motifs,bv]
      rfl
    · intro j
      exact (qt j).changeSizes (by dsimp only [M]; rw [shrinkBinary_next_base,bv])
  have parsed : ∀ n,T.prefixOK (i+n) ↔ Run.PrefixOK n (.step M next) E raw := by
    intro n
    exact (reads n).trans (Program.prefix_changeTable (n:=n) eqv X (.step M next) stepTable raw)
  have last (v : Run.WireLayer) (suffix : List Bool) : T.outcome v suffix ↔ (Run.step M next).EndsAt E raw v suffix := by
    exact (ends v suffix).trans (Program.endsAt_changeTable eqv X (.step M next) stepTable raw v suffix)
  have cm : Q.motifs=op.motifs := by
    rw [shrinkBinaryFamily_motifs]; dsimp only [op,dims₀];rw [nb];rfl
  have edge : dims₀.oldEdges=Fintype.card B.Base*2^s := by dsimp only [dims₀,Dimensions.oldEdges];rw [nb];rfl
  have lanes : dims₀.originalLanes=2^(shrinkCharge s+b) := by
    dsimp [dims₀,Dimensions.originalLanes,dims,shrinkStage,shrinkCharge,pow_add];ring
  have gspan:=vc.graphBound
  have wspan:=vc.widthBound
  have graph : csr.graph+6*dims₀.oldEdges≤csr.heap := by rw [edge];exact gspan
  have widths : csr.width+dims₀.oldEdges*dims₀.originalLanes≤csr.heap := by rw [edge,lanes];exact wspan
  have capQ : W*(T.archive.K*(past.map Stage.motifs).sum)+Q.motifs*T.archive.K*W≤T.capacity := by
    rw [cm]
    exact cap
  have active {np nr nk : ℕ} (machine : Machine W np nr nk) :=
    shrink_on_archive T.archive G s (2^t) b (Nat.two_pow_pos _) ok B T.field T.age T.current m
      past rest T.edges T.capacity T.bits fit hb.1 (fixed _ List.mem_cons_self) volume
      (ce.1.trans smallZ) vc.live limits.origin limits.tables dense later
      (later.trans vc.graphLow) (later.trans vc.widthLow) graph widths control capQ vc.stored machine
  have fullTimes (j : Fin M.rules.count) := Program.native_shrink_step G small tail (a).K T.current csr rem B j
  have access : shrinkBudget G s (2^t) b (Nat.two_pow_pos _) ok B (a).K T.current csr≤T.clock := by
    rw [shrinkBudget_absolute]
    rw [bv]
    exact (Nat.le_add_right ..).trans time
  intro np nr nk machine
  refine TickStageSpec.Admission.mono (b:=row.block) (data:=row.publicData) (field:=T.field)
    (pre:=fun input=>input=m) (good:=fun _=>((Q.record fit).read (raw.take (Q.record fit).width)).isSome)
    (t:=shrinkBudget G s (2^t) b (Nat.two_pow_pos _) ok B (a).K T.current csr) (@active)
    (fun _=>id) (fun _ _=>T.first_record M next E raw parsed) ?_ access machine
  rintro _ out _ _ ⟨j,hit,live,st,record⟩
  have nodeCount:=shrinkBinary_next_base G s (2^t) b (Nat.two_pow_pos _) ok B j
  have actualRows : dims₀.newEdges=Fintype.card (M.next j).Base*2^t := by
    rw [nodeCount];dsimp only [dims₀,Dimensions.newEdges,Dimensions.newBase];rw [nb];rfl
  have actualBits : dims₀.newEdges*dims₀.residual=(M.next j).edgeCount := by rw [actualRows];rfl
  have live':(a).Live T.stages T.edges T.bits T.current (allocate (a).K csr op).next out:=by simpa only [dir'] using live
  have vv:=T.next_visit past op (M.next j) out actualRows actualBits live' st
  have clockAtBase : Program.nativeTicks T.archive.K T.current P csr rem (Fintype.card B.Base)≤T.clock := by
    simpa only [bv] using time
  have times:=(fullTimes j).symm.le.trans clockAtBase
  have pastEq:=T.past_next past op
  let timeStage (base : ℕ) := Stage.shrink (dims (shrinkStage s (2^t)) base (CompressorPacking.tagBits (2^s)) b)
  let pastCursor := finish T.archive.K (past++[op]) T.archive.cursor
  let timeCursor := (allocate T.archive.K csr (timeStage (Fintype.card B.Base))).next
  have cursorEq : pastCursor=timeCursor :=
    pastEq.trans (congrArg (fun st => (allocate T.archive.K csr st).next) (congrArg timeStage nb))
  let remainingTime (c : Cursor) := Program.nativeTicks T.archive.K T.current tail c rem (Fintype.card (M.next j).Base)
  have atTimeCursor : remainingTime timeCursor≤T.clock :=
    (Nat.le_add_left (remainingTime timeCursor)
      (shrinkBudget G s (2^t) b (Nat.two_pow_pos _) ok B T.archive.K T.current csr)).trans times
  have paidTime : remainingTime pastCursor≤T.clock := (congrArg remainingTime cursorEq).le.trans atTimeCursor
  have dnext : T.stages=(past++[op])++tail.directory rem (Fintype.card (M.next j).Base) := by
    rw [nodeCount,dir',List.append_assoc];rfl
  have key (n : ℕ):=T.next_parses (n:=n) M next E raw parsed j hit
  have cut:=T.drop_record past op Q fit cm
  have dirOne := directory_tail_eq past T.stages ((P).directory rem (Fintype.card X.Base))
    (tail.directory rem (Fintype.card (M.next j).Base)) op dir dnext
  let remaining := (List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop
    (W*(T.archive.K*((past++[op]).map Stage.motifs).sum))
  have consumed : raw.drop E.1.width=remaining := cut
  let here : T.Point (i+1) out :=
    { s:=t,rem:=rem,program:=tail,state:=M.next j,ceiling:=Z,reach:=ce.2 j,fits:=laterBounds,small:=smallZ
      fixed:=fun b h=>fixed b (List.mem_cons_of_mem _ h)
      past:=past++[op],index:=by simp [idx],directory:=dnext,text:=(T.row_after _ _ text).2
      visit:=vv,time:=paidTime
      parses:=by
        intro table bits n
        change T.prefixOK (i+1+n) ↔ Run.PrefixOK n (next j) (E.2 j) remaining
        rw [←consumed]
        exact key n
      complete:=by
        intro tailBits final cont
        apply complete final
        have pos : 0<csr.width := by
          have low : T.archive.cursor.dense≤csr.width:=vc.widthLow
          have header : csr.header+64≤T.archive.cursor.dense:=later
          omega
        exact ⟨m,out,fit,j,(fun _ _=>rfl),hit,dirOne,⟨fixed _ List.mem_cons_self,volume,ce.1.trans smallZ,pos,control⟩,⟨⟨vc.graphLow,vc.widthLow,vc.graphBound,vc.widthBound⟩,vc.stored⟩,record,(by simpa only [tailBits,pastEq,←cut] using cont)⟩
      outcome:=by
        intro table bits v suffix
        change T.outcome v suffix ↔ (next j).EndsAt (E.2 j) remaining v suffix
        rw [←consumed]
        exact (last v suffix).trans (Run.endsAt_step M next E raw j hit v suffix) }
  refine ⟨⟨here⟩,record.archive _ (by have:=T.counterHigh;omega) ?_ (.inr (control.trans T.counterHigh.le))⟩
  change T.counter.val ≠ csr.header+27
  have rawEnd : (a).cursor.dense+(a).histWords (past++op::rest)≤csr.heap := dense
  have heapEnd : (allocate (a).K csr op).next.heap≤T.current.val := control
  rw [heap_step] at heapEnd
  have beforeHeap : csr.header+64≤csr.heap :=
    later.trans ((Nat.le_add_right _ _).trans rawEnd)
  have headerEnd : csr.header+64≤T.current.val :=
    beforeHeap.trans ((Nat.le_add_right _ _).trans heapEnd)
  exact (Nat.ne_of_lt (((Nat.add_lt_add_left (by decide : 27<64) csr.header).trans_le headerEnd).trans T.counterHigh)).symm



end Shrink

section Refresh
open RefreshDemandRows RefreshTies RefreshStageNav
variable {s t h pad i : ℕ} {g : Fin (2^s)→Fin (2^s)→ℕ} {γ C : ℝ}
    {G : RefreshMotif.Table F g (1+h+pad) C} {hm : 2≤2^s} {hh : 0<h} {sym : ∀ i j,g i j=g j i}
    {rows : ∀ i,∑ j,g i j=h} {zero : ∀ i,g i i=0} {conn : Expander.Bound (Expander.transition g h) ℝ γ}
    {degree : 1+h+pad=2^t} (tail : Program F t)
local notation "P" => Program.refresh s t h pad g γ C G hm hh sym rows zero conn degree tail

theorem refresh_point (rem Z : ℕ) (X : State (2^s) ((P).charge+rem)) (m : Memory W)
    (reach : ((P).run rem X).WidthCeiling Z) (bounds : ∀ b∈(P).recordBounds,b.1≤(a).K ∧ b.2*Z<2^W)
    (smallZ : Z≤(2^(u^10))^4) (fixed : ∀ b∈wordConstants P,b≤u)
    (past : List Stage) (idx : past.length=i) (dir : T.stages=past++(P).directory rem (Fintype.card X.Base))
    (text : T.procedures.drop i=nativeRows T.current (a).K P) (vis : (a).Visit T.stages T.edges T.bits T.current past X m)
    (time : Program.nativeTicks (a).K T.current P (finish (a).K past (a).cursor) rem (Fintype.card X.Base)≤T.clock)
    (reads : let q:=(P).table (a).K W Z bounds rem X reach
      let raw:=(List.ofFn (fun i : Fin T.capacity=>T.bits i.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ n,T.prefixOK (i+n) ↔ Run.PrefixOK n ((P).run rem X) q.records raw)
    (complete : let raw:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ final,(a).Journal u T.current T.counter P rem X (finish (a).K past (a).cursor) raw m final → T.journal final)
    (ends : let q:=(P).table (a).K W Z bounds rem X reach
      let raw:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ v rest,T.outcome v rest ↔ ((P).run rem X).EndsAt q.records raw v rest) :
    let row:=refresh T.current (a).K s h pad G sym rows zero
    TickStageSpec.Admission T.field row.block row.publicData (fun x=>x=m) (fun _=>T.prefixOK (i+1))
      (fun _ out=>Nonempty (T.Point (i+1) out) ∧ out T.counter.val=m T.counter.val) T.clock := by
  intro row
  let b:=tail.charge+rem
  let eqv:=Nat.add_assoc s tail.charge rem
  let B : State (2^s) (s+b):=eqv ▸ X
  let R:=refreshBinary G B hm hh sym rows zero conn
  let M:=Program.recastMove degree R
  let next:=fun j=>tail.run rem (M.next j)
  let Q:=refreshBinaryFamily G B hm hh sym rows zero conn
  let op:=Stage.refresh (Fintype.card B.Base) (2^s) (2^b) h pad
  let rest:=tail.directory rem ((Fintype.card B.Base)*2^s)
  let csr:=finish (a).K past (a).cursor
  let raw:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
  have bv : Fintype.card B.Base=Fintype.card X.Base:=Program.baseCast eqv X
  have dir' : T.stages=past++op::rest := by dsimp only [op,rest];rw [bv];exact dir
  have limits:=T.limits
  rw [dir'] at limits
  obtain ⟨dense,later,control,volume,cap⟩:=limits.at_step
  have vc:=vis.cast eqv
  change (a).Visit T.stages T.edges T.bits T.current past B m at vc
  rw [dir'] at vc
  have ce : (Run.step M next).WidthCeiling Z:=Program.beforeRecast eqv X _ reach
  have hb:=bounds _ List.mem_cons_self
  have fit : Q.Fits (a).K W:=refreshBinaryFamily_fits G B hm hh sym rows zero conn hb.1
    ((Nat.mul_le_mul_left _ (by simpa [Nat.add_comm] using ce.1)).trans_lt hb.2)
  let laterBounds : ∀ b∈tail.recordBounds,b.1≤(a).K ∧ b.2*Z<2^W:=fun j h=>bounds j (List.mem_cons_of_mem _ h)
  let qt:=fun j=>tail.table (a).K W Z laterBounds rem (M.next j) (ce.2 j)
  let transported:=Program.degreeFamily degree R (Fintype.card B.Base*2^b) (Fintype.card B.Base*2^s) Q fit
    rfl (refreshBinary_next_base G B hm hh sym rows zero conn)
  let E : (Run.step M next).Records:=((transported.1.record transported.2.1),fun j=>(qt j).records)
  have read : E.1.read (raw.take E.1.width)=((Q.record fit).read (raw.take (Q.record fit).width)).map
      (Program.degreeTerm degree R) :=
    Program.degree_read degree R (Fintype.card B.Base*2^b) (Fintype.card B.Base*2^s)
      Q fit rfl (refreshBinary_next_base G B hm hh sym rows zero conn) raw
  have width : E.1.width=(Q.record fit).width := by
    change transported.1.motifs*(a).K*W=Q.motifs*(a).K*W
    rw [transported.2.2.1];rfl
  let stepTable : Program.RecordTable (Run.step M next) T.archive.K W
      ((Fintype.card X.Base * 2^b) :: (tail.directory rem (Fintype.card X.Base * 2^s)).map Stage.motifs) :=
    Program.consTable M next transported.1 transported.2.1
      (transported.2.2.1.trans (congrArg (fun card => card * 2^b) bv))
      (fun j => (qt j).changeSizes (congrArg (fun card => (tail.directory rem card).map Stage.motifs)
        ((transported.2.2.2 j).trans (congrArg (fun card => card * 2^s) bv))))
  have parsed : ∀ n,T.prefixOK (i+n) ↔ Run.PrefixOK n (.step M next) E raw := by
    intro n
    exact (reads n).trans (Program.prefix_changeTable (n := n) eqv X (.step M next) stepTable raw)
  have last (v : Run.WireLayer) (suffix : List Bool) : T.outcome v suffix ↔ (Run.step M next).EndsAt E raw v suffix := by
    exact (ends v suffix).trans (Program.endsAt_changeTable eqv X (.step M next) stepTable raw v suffix)
  have widths:=vc.widthBound
  change csr.width+(Fintype.card B.Base*2^s)*2^(s+b)≤csr.heap at widths
  rw [pow_add] at widths
  have active {np nr nk : ℕ} (machine : Machine W np nr nk) :=
    refresh_on_archive a G B hm hh sym rows zero conn T.field T.age T.current m past rest T.edges
      T.capacity T.bits fit hb.1 (fixed _ List.mem_cons_self) T.alphabet volume (ce.1.trans smallZ)
      vc.live limits.origin limits.tables dense later vc.graphBound widths control cap vc.stored machine
  have access : refreshCallTime G B sym rows zero (a).K T.current csr≤T.clock := by
    rw [refreshCallTime_absolute]
    rw [bv]
    exact (Nat.le_add_right ..).trans time
  intro np nr nk machine
  refine TickStageSpec.Admission.mono (b:=row.block) (data:=row.publicData) (field:=T.field)
    (pre:=fun input=>input=m) (good:=fun _=>((Q.record fit).read (raw.take (Q.record fit).width)).isSome)
    (t:=refreshCallTime G B sym rows zero (a).K T.current csr) (@active) (fun _=>id)
    (fun _ _=>by rw [T.first_record M next E raw parsed,read];simp) ?_ access machine
  rintro _ out _ _ ⟨j,hit,live,st,published,descriptors,frame⟩
  let j':=Program.degreeTerm degree R j
  have selected : E.1.read (raw.take E.1.width)=some j' := by rw [read,hit];rfl
  have actualBase:=refreshBinary_next_base G B hm hh sym rows zero conn j
  have nodeCount:=transported.2.2.2 j'
  have actualRows : (RefreshStageLayout.counts (Fintype.card B.Base) (2^s) (2^b) h pad).newGraphRows=
      Fintype.card (R.next j).Base*(1+h+pad) := by rw [actualBase];rfl
  have actualBits : (RefreshStageLayout.counts (Fintype.card B.Base) (2^s) (2^b) h pad).newWidthSpan=
      (R.next j).edgeCount := by rw [State.edgeCount,actualBase];rfl
  have live':(a).Live T.stages T.edges T.bits T.current (allocate (a).K csr op).next out:=by simpa only [dir'] using live
  have vv:=(T.next_visit past op (R.next j) out actualRows actualBits live' st).redegree degree
  rw [Program.degree_next] at vv
  have localTime:=Program.native_refresh_step G hm hh sym rows zero conn degree tail (a).K T.current csr rem B j
  rw [actualBase,bv] at localTime
  have pastEq:=T.past_next past op
  have dnext : T.stages=(past++[op])++tail.directory rem (Fintype.card (M.next j').Base) := by
    rw [nodeCount,dir',List.append_assoc];rfl
  have key (n : ℕ):=T.next_parses (n:=n) M next E raw parsed j' selected
  have cut:=T.drop_record past op Q fit (by rfl)
  have dirOne : (P).directory rem (Fintype.card X.Base)=op::tail.directory rem (Fintype.card (M.next j').Base) := by
    have eq : past++(P).directory rem (Fintype.card X.Base)=past++(op::tail.directory rem (Fintype.card (M.next j').Base)) := by
      rw [←dir,dnext,List.append_assoc];rfl
    simpa only [List.append_cancel_left_eq] using eq
  let remaining := (List.ofFn (fun j : Fin T.capacity => T.bits j.val)).drop
    (W*(T.archive.K*((past++[op]).map Stage.motifs).sum))
  have consumed : raw.drop E.1.width=remaining := by
    rw [width]
    exact cut
  let here : T.Point (i+1) out :=
    { s:=t,rem:=rem,program:=tail,state:=M.next j',ceiling:=Z,reach:=ce.2 j',fits:=laterBounds,small:=smallZ
      fixed:=fun b h=>fixed b (List.mem_cons_of_mem _ h)
      past:=past++[op],index:=by simp [idx],directory:=dnext,text:=(T.row_after _ _ text).2
      visit:=vv,time:=by
        rw [pastEq,nodeCount]
        dsimp only [op]
        rw [bv]
        exact (Nat.le_add_left _ (refreshCallTime G B sym rows zero (a).K T.current csr)).trans
          (localTime.symm.le.trans time)
      parses:=by
        intro table bits n
        change T.prefixOK (i+1+n) ↔ Run.PrefixOK n (next j') (E.2 j') remaining
        rw [←consumed]
        exact key n
      complete:=by
        intro tailBits final cont
        apply complete final
        have pos : 0<csr.width := by
          have low : (a).cursor.dense≤csr.width := vc.widthLow
          have header : csr.header+64≤(a).cursor.dense := later
          omega
        exact ⟨m,out,fit,j,(fun _ _=>rfl),hit,dirOne,
          ⟨fixed _ List.mem_cons_self,volume,ce.1.trans smallZ,pos,control⟩,
          ⟨⟨vc.graphLow,vc.widthLow,vc.graphBound,vc.widthBound⟩,vc.stored⟩,
          published,⟨descriptors.1,descriptors.2.1,
            by simpa only [rest,Program.directory_length] using descriptors.2.2⟩,
          frame,by simpa only [tailBits,pastEq,←cut] using cont⟩
      outcome:=by
        intro table bits v suffix
        change T.outcome v suffix ↔ (next j').EndsAt (E.2 j') remaining v suffix
        rw [←consumed]
        exact (last v suffix).trans (Run.endsAt_step M next E raw j' selected v suffix) }
  exact ⟨⟨here⟩,frame _ (by have:=T.counterHigh;omega) (.inr (control.trans T.counterHigh.le))⟩


end Refresh

/-- Every installed physical word-row is one of the two actual branch parsers. The
remaining typed program determines which native instruction generator runs at this index. -/
theorem step {i : ℕ} {m : Memory W} (here : T.Point i m) (row : Procedure W)
    (access : T.procedures[i]?=some row) :
    TickStageSpec.Admission T.field row.block row.publicData (fun x=>x=m) (fun _=>T.prefixOK (i+1))
      (fun _ out=>Nonempty (T.Point (i+1) out) ∧ out T.counter.val=m T.counter.val) T.clock := by
  obtain ⟨s,rem,P,X,Z,reach,bounds,smallZ,fixed,past,idx,dir,text,vis,time,reads,complete,ends⟩:=here
  have hd : (T.procedures.drop i)[0]?=some row := by simpa using access
  rw [text] at hd
  cases P with
  | done s => simp [nativeRows] at hd
  | shrink s t G small tail =>
    change some (shrink T.current (a).K s (2^t) G)=some row at hd
    cases Option.some.inj hd
    intro np nr nk machine
    exact T.shrink_point tail rem Z X m reach bounds smallZ fixed past idx dir text vis time reads complete ends machine
  | refresh s t h pad g γ C G hm hh sym rows zero conn degree tail =>
    change some (refresh T.current (a).K s h pad G sym rows zero)=some row at hd
    cases Option.some.inj hd
    intro np nr nk machine
    exact T.refresh_point tail rem Z X m reach bounds smallZ fixed past idx dir text vis time reads complete ends machine

/-- A concrete remaining physical row family, its genuine parsed-prefix cutoff, and the
complete external-memory representation are carried across the installed counted ROM. -/
def timeline (B : Block F) (n : ℕ)
    (code : T.procedures=nativeRows T.current (a).K (B.repeat n))
    (shorten : ∀ i j,i≤j→T.prefixOK j→T.prefixOK i) :
    CountedTimeline T.field T.counter (nativeRows T.current (a).K (B.prefix (.done _))) n where
  resident i m := Nonempty (T.Point i m)
  good := T.prefixOK
  cost _ := T.clock
  seen i m p := let ⟨v⟩:=p; v.seen T
  shorten := shorten
  step q hq j m here := by
    obtain ⟨v⟩:=here
    apply T.step v (List.get _ j)
    rw [code]
    have atRow:=repeated_get T.current (a).K B n q hq j
    exact List.getElem?_eq_getElem _ |>.trans (congrArg some atRow)
  decrement q hq m here _ := ⟨(here.some).decrement T _⟩

theorem Point.finished {m : Memory W} (p : T.Point T.procedures.length m) :
    let raw := (List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*(a).histWords T.stages)
    T.journal m ∧ ∃ v : Run.WireLayer,T.outcome v raw ∧ (a).Visit T.stages T.edges T.bits T.current T.stages v.state m := by
  intro raw
  rcases p with ⟨s,rem,P,X,Z,reach,bounds,smallZ,fixed,past,idx,dir,text,vis,time,reads,complete,ends⟩
  rw [List.drop_length] at text
  cases P with
  | done s =>
    have eq : T.stages=past := by simpa [Program.directory] using dir
    have bytes : W*(a).histWords T.stages=W*((a).K*(past.map Stage.motifs).sum) := by rw [eq];rfl
    let layer : Run.WireLayer:=⟨2^s,0+rem,X⟩
    refine ⟨?_,layer,(ends layer raw).mpr ?_,?_⟩
    · apply complete m
      change exceptCounter T.counter m m
      exact fun _ _ => rfl
    · refine ⟨(),?_,rfl⟩
      dsimp only [raw]
      rw [bytes]
      rfl
    · change (a).Visit T.stages T.edges T.bits T.current T.stages X m
      simpa only [eq] using vis
  | shrink _ _ _ _ tail => simp [nativeRows] at text
  | refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => simp [nativeRows] at text


end Traversal

private theorem wordConstants_cast {s t : ℕ} (e : s=t) (P : Program F s) :
    wordConstants (e ▸ P : Program F t)=wordConstants P := by cases e;rfl

private theorem wordConstants_shrinks (B : Block F) (n i : ℕ) (P : Program F (B.exponent (i+n))) :
    wordConstants (B.shrinkPrefix n i P)=B.shrinkConstants n i++wordConstants P := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [Block.shrinkPrefix,Block.shrinkConstants,wordConstants,ih,
      wordConstants_cast,List.cons_append]

def fixedMoveWords (B : Block F) := B.shrinkWordCap+refreshFixedWords B.refresh

theorem repeated_fixed (B : Block F) (n : ℕ) {b : ℕ} (mem : b∈wordConstants (B.repeat n)) :
    b≤fixedMoveWords B := by
  have prefix_words (P : Program F (B.exponent 0)) : wordConstants (B.prefix P)=
      B.shrinkConstants B.levels 0++refreshFixedWords B.refresh::wordConstants P := by
    simp only [Block.prefix,wordConstants_shrinks,wordConstants_cast,wordConstants]
  induction n with
  | zero => simp [Block.repeat,wordConstants] at mem
  | succ n ih =>
    rw [Block.repeat,prefix_words,List.mem_append,List.mem_cons] at mem
    rcases mem with present | same | earlier
    · have shrinkCap : b≤B.shrinkWordCap := List.le_sum_of_mem present
      exact shrinkCap.trans (Nat.le_add_right B.shrinkWordCap (refreshFixedWords B.refresh))
    · rw [same];exact Nat.le_add_left ..
    · exact ih earlier

theorem cursor_record_fits (B : Block F) {u rem low off slots e : ℕ} (hu : e+40≤u)
    (half : low≤u^10) (growth : B.widthBase≤u) (factor : B.repeatFactor≤u)
    (slot : off*slots*3≤u^e) (hk : 2≤(B.repeat (u^8)).charge+rem) :
    let X:=B.cursorState hk low off slots
    let z:=(X.maxWidth+1)*B.widthBase^(u^8)
    ((B.repeat (u^8)).run rem X).WidthCeiling z ∧ z≤(2^(u^10))^4 ∧
      ∀ b∈(B.repeat (u^8)).recordBounds,b.1≤B.alphabetCap ∧ b.2*z<2^(16*u^10) := by
  intro X z
  refine ⟨B.repeat_widthCeiling _ rem X,B.cursor_width_word_space hu half growth slot hk,?_⟩
  intro b mem
  exact ⟨Block.component_le Prod.fst (B.bounds_repeat _ mem),
    (Nat.mul_le_mul_right z (Block.component_le Prod.snd (B.bounds_repeat _ mem))).trans_lt
      (B.cursor_repeat_word hu half growth factor slot hk)⟩

open scoped Fin.CommRing in
/-- Actual directory, histogram and heap extents in the four installed address banks. -/
theorem Parameters.cursor_limits [Fintype F] (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u) (levels : B.levels+1≤u)
    (alloc : B.allocations.sum≤u) (score : B.costFactors.sum≤u) (symbols : B.alphabetCap≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (bits : shape.bits=2^(u^10-u^4)) (edges : ℕ) :
    let p:=Parameters.cursor B u rem low stride cells shape off tariff
    let a:=p.archive (2^B.exponent 0) (16*u^10)
    let steps:=(B.repeat (u^8)).directory rem p.axes
    a.Limits u (a.control:Word (16*u^10)) steps edges a.pairCapacity := by
  intro p a steps
  let v:=2^(u^10)
  let chunk:=2^(u^10-u^4)
  have chunkWord : chunk≤v := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have inStride : v≤TickWorkspace.stride u := Nat.le_self_pow (by decide : 4≠0) _
  have floor : 40<v := hu.trans_lt ((Nat.le_self_pow (by decide : 10≠0) u).trans_lt Nat.lt_two_pow_self)
  have large : 40<TickWorkspace.stride u := floor.trans_le inStride
  have ctr : ((a.control:Word (16*u^10))).val=TickWorkspace.base u 40 :=
    Nat.mod_eq_of_lt ((by omega : TickWorkspace.base u 40<TickWorkspace.base u 40+TickWorkspace.stride u).trans
      (TickWorkspace.word_space (by omega) large))
  have heap : 8*(steps.map Stage.heapWords).sum≤chunk := B.cursor_heap_space hu levels alloc half depth
  have raw : 8*(a.histWords steps*(16*u^10))≤chunk := by
    change 8*((B.alphabetCap*(steps.map Stage.motifs).sum)*(16*u^10))≤chunk
    rw [Nat.mul_comm B.alphabetCap]
    exact B.cursor_histogram_space hu symbols levels score half depth
  have bytes : a.histWords steps≤a.histWords steps*(16*u^10) := Nat.le_mul_of_pos_right _ (by positivity)
  have length : steps.length=(B.levels+1)*u^8 := by
    rw [show steps=(B.repeat (u^8)).directory rem p.axes from rfl,Program.directory_length,program_length,B.repeat_effects_length]
  have nine : steps.length≤u^9 := calc
    steps.length = (B.levels+1)*u^8 := length
    _ ≤ u*u^8 := Nat.mul_le_mul_right (u^8) levels
    _ = u^9 := by rw [pow_succ u 8, Nat.mul_comm u (u^8)]
  have size : 64*(steps.length+2)≤TickWorkspace.stride u := by
    have two : 2≤u^9 := (by omega : 2≤u).trans (Nat.le_self_pow (by decide) _)
    have square : 128≤u^2 := by rw [pow_two];nlinarith [Nat.mul_le_mul hu hu]
    have h : 64*(steps.length+2)≤u^11 := calc
      _ ≤ 128*u^9 := by omega
      _ ≤ u^2*u^9 := Nat.mul_le_mul_right _ square
      _ = u^11 := by ring
    exact h.trans ((width_pow_le_two_pow_sq (by omega : 11≤u)).trans
      ((Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by omega : 0<u) (by decide : 2≤10))).trans inStride))
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · rw [Archive.directory_length]
    exact (Nat.add_le_add_left size _).trans (TickWorkspace.apart (by decide : 20<21))
  · have h : a.histWords steps≤TickWorkspace.stride u := by omega
    exact (Nat.add_le_add_left h _).trans (TickWorkspace.apart (by decide : 21<22))
  · rw [ctr]
    have h : (steps.map Stage.heapWords).sum≤TickWorkspace.stride u := by omega
    exact (Nat.add_le_add_left h _).trans (TickWorkspace.apart (by decide : 22<40))
  · omega
  · change (16*u^10)*a.histWords steps≤ shape.bits/2
    rw [bits,Nat.mul_comm];change a.histWords steps*(16*u^10)≤chunk/2;omega

/-- Execute the counted native compression instructions from the real initialized cursor.
Failure of the adaptive parser forces zero mass. Success returns the graph belonging to
the same parsed branch, its unchanged dense histogram and the final directory pointer. -/
theorem Archive.run_repeated {u : ℕ} (a : Archive) (B : Block F) (n rem : ℕ)
    (X : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (field : FieldCode F (16*u^10)) (cur ctr : Word (16*u^10)) (edges cap Z : ℕ) (bits : ℕ→Bool)
    (origin : Memory (16*u^10)) (age : 40≤u) (alphabet : a.K≤u) (counter : cur.val<ctr.val)
    (bounds : ∀ b∈(B.repeat n).recordBounds,b.1≤a.K ∧ b.2*Z<2^(16*u^10))
    (reach : ((B.repeat n).run rem X).WidthCeiling Z) (small : Z≤(2^(u^10))^4)
    (fixed : ∀ b∈wordConstants (B.repeat n),b≤u) :
    let P:=B.repeat n
    let steps:=P.directory rem (Fintype.card X.Base)
    let q:=P.table a.K (16*u^10) Z bounds rem X reach
    let raw:=List.ofFn (fun j : Fin cap=>bits j.val)
    let localSteps:=Program.nativeTicks a.K cur P a.cursor rem (Fintype.card X.Base)
    let rows:=(B.prefix (.done _)).length
    let p:=repeated cur ctr a.K B
    a.Limits u cur steps edges cap →
    TickStageSpec.Admission field p.block p.publicData
      (fun m=>m=origin ∧ a.Visit steps edges bits cur [] X m ∧ (m ctr.val).val=n)
      (fun _=>((P.run rem X).plan.read q.codes raw).isSome)
      (fun _ out=>a.Journal u cur ctr P rem X a.cursor raw origin out ∧ ∃ v : Run.WireLayer, (P.run rem X).EndsAt q.records raw v (raw.drop ((16*u^10)*a.histWords steps)) ∧
        a.Visit steps edges bits cur steps v.state out)
      (n*(7+(rows*(rows*localSteps)+1))+4) := by
  intro P steps q raw localSteps rows p limits
  let R:=P.run rem X
  let T : Traversal F u :=
    { archive:=a,field:=field,current:=cur,counter:=ctr,stages:=steps,procedures:=nativeRows cur a.K P
      edges:=edges,capacity:=cap,bits:=bits,clock:=localSteps,prefixOK:=fun i=>Run.PrefixOK i R q.records raw
      journal:=a.Journal u cur ctr P rem X a.cursor raw origin,outcome:=R.EndsAt q.records raw,limits:=limits,age:=age,alphabet:=alphabet,counterHigh:=counter }
  have shorter (i j : ℕ) (h : i≤j) : T.prefixOK j→T.prefixOK i := Run.PrefixOK.shorten h R q.records raw
  let timeline:=T.timeline B n rfl shorter
  have count : n*(nativeRows cur a.K (B.prefix (.done _))).length=T.procedures.length :=
    (repeated_length cur a.K B n).symm
  have size : T.procedures.length=P.length := nativeRows_length cur a.K P
  intro np nr nk machine
  refine TickStageSpec.Admission.mono
    (fun {labels registers slots} M => repeated_admission field cur ctr a.K B n timeline M)
    ?_ ?_ ?_ ?_ machine
  · rintro m ⟨rfl,vis,ctrAt⟩
    constructor
    · refine ⟨{
        s := B.exponent 0
        rem := rem
        program := P
        state := X
        ceiling := Z
        reach := reach
        fits := bounds
        small := small
        fixed := fixed
        past := []
        index := rfl
        directory := rfl
        text := rfl
        visit := vis
        time := le_rfl
        parses := ?_
        complete := ?_
        outcome := ?_ }⟩
      · dsimp only
        intro k
        simp [T,q,raw,R]
      · dsimp only
        intro final cont
        simpa [T,raw,finish] using cont
      · dsimp only
        intro v suffix
        simp [T,q,raw,R]
    · exact ctrAt
  · intro m hm
    change ((P.run rem X).plan.read q.codes raw).isSome ↔ Run.PrefixOK _ R q.records raw
    rw [count,size]
    exact (Run.PrefixOK.complete _ (P.stageLength_run rem X) q.records raw).symm
  · intro _ o _ _ result
    have h : Nonempty (T.Point T.procedures.length o) := by
      change Nonempty (T.Point _ o) at result
      simpa only [count] using result
    exact h.some.finished T
  · simp [timeline,Traversal.timeline,CountedTimeline.perRow,T,rows,nativeRows_length]




end
end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass

open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure PhysicalStage
open CompressorPacking Native NavigationDirectory HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

structure RowContents {s : Layer} (d : LayerData s) («protected» : ℕ→Prop) (mem : ℕ→ℕ)
    (halfCap motifCap : ℕ) : Prop where
  reads : d.Reads mem
  footprint : d.Footprint «protected» mem
  halves : ∀ j,(d.halfWidth j).length≤halfCap
  motifs : s.kind≠0 → ∀ j,(d.motifCopies j).length≤ motifCap

structure ArchivedSource (row : NodeRow) («protected» : ℕ→Prop) (mem : ℕ→ℕ) (halfCap motifCap : ℕ) : Prop where
  contents : RowContents row.data «protected» mem halfCap motifCap
  parents : ParentReads row.parent row.owners mem
  ownerCells : row.parent.finalLayer=false → ∀ j : Fin row.layer.count,«protected» (row.parent.owners+j.val)

/-- A receipt retains the same chosen row and its committed physical pass, including all
native descriptor words in the issued memory and their persistence into the named RAM. -/
def RecordedStep {W : ℕ} (K : ℕ) (cur ctr : Word W) (headerEnd heapEnd : ℕ) (final : Memory W) :
    Move.VisitPredicate F :=
  fun R j old charge row=>ShrinkVisit K cur ctr headerEnd heapEnd final R j old charge row ∨
    RefreshVisit K cur ctr headerEnd heapEnd final R j old charge row

theorem RecordedStep.transfer {W K headerEnd heapEnd : ℕ} {cur ctr : Word W} {final out : Memory W}
    (same : ∀ x,x<heapEnd→ out x=final x) {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (b : Fin R.rules.count) (O : A.ArchiveSites) (charge : (R.next b).Site→ℕ) (row : R.ArchiveStep b O charge) :
    RecordedStep K cur ctr headerEnd heapEnd final R b O charge row →
      RecordedStep K cur ctr headerEnd heapEnd out R b O charge row :=
  Or.imp (fun s=>s.transfer same) (fun r=>r.transfer same)

private theorem saved_after {a : Archive} {u s : ℕ} {cur ctr : Word (16*u^10)}
    (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem)) (c : Cursor) (raw : List Bool)
    {out final : Memory (16*u^10)} (tail : a.Journal u cur ctr P rem X c raw out final) :
    SavedFrame cur ctr (finish a.K (P.directory rem (Fintype.card X.Base)) c).header c.header c.heap out final :=
  fun _x hc ht hdr low=>Archive.Journal.frame P rem X c raw tail hc ht ⟨hdr,Or.inl low⟩

/-- Reconstruction keeps the actual parsed history, its typed numerical owners, and the
unconsumed suffix from the same ordered physical alternatives. -/
def Recovered {d l : ℕ} {A : State d l} (r : Run F A) (E : r.Records) (C : r.Charges)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool)
    (vis : Move.VisitPredicate F) (J : ∀ Pins : Type, r.Assembler Pins)
    (wordVis : ∀ Pins : Type, Run.WordVisit F Pins) (post : List NodeRow→Layer→Prop) : Prop :=
  ∃ (h : r.plan.History) (suffix : List Bool) (p : r.ArchivePath h C O),
    r.plan.read (r.codes E) raw=some (h,suffix) ∧ r.FinalNumbered h C O p ∧ r.ArchiveVisits vis h C O p ∧
      (∀ (Pins : Type) (L : A.Words Pins),r.WordVisits (wordVis Pins) h (J Pins).steps L C O p) ∧ post (r.archiveList h C O p data) (r.finalArchive h C O p).1

private def castSites {d l L : ℕ} (e : l=L) (A : State d l) (O : A.ArchiveSites) :
    (e ▸ A : State d L).ArchiveSites :=
  ⟨O.layer,by cases e;exact O.ord⟩

private theorem numbered_castSites {d l L : ℕ} (e : l=L) (A : State d l) (O : A.ArchiveSites)
    (numbered : O.Numbered) : (castSites e A O).Numbered := by cases e;exact numbered

private theorem recovered_recast {d l L k w tariff : ℕ} (e : l=L) (A : State d l) (r : Run F (e ▸ A : State d L))
    {sizes : List ℕ} (table : Program.RecordTable r k w sizes) (C : Program.Certified r tariff)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool) (vis : Move.VisitPredicate F)
    (J : ∀ Pins : Type, r.Assembler Pins) (wordVis : ∀ Pins : Type, Run.WordVisit F Pins)
    (post : List NodeRow→Layer→Prop) :
    Recovered r table.records C.1 (castSites e A O) data raw vis J wordVis post →
    Recovered (Program.recast e A r) (Program.changeTable e A r table).records
      (Program.certRecast e A r C).1 O data raw vis (fun Pins=>Run.inputAssembler e A r (J Pins)) wordVis post := by cases e;exact id

private theorem initial_fits {K W : ℕ} (ops : List Stage) (c : Cursor) (s : Layer)
    (fit : ∀ q ∈ nodeLayers K ops c s,q.actual.first+q.actual.count≤2^W) :
    s.first+s.count≤2^W := by
  cases ops <;> exact fit _ (List.mem_cons_self ..)

private def interleave {d l D L : ℕ} {A : State d l} (R : Move F A D L) (t : Fin R.rules.count)
    (old : A.ArchiveSites) {charge : (R.next t).Site→ℕ} (step : R.ArchiveStep t old charge)
    (data : LayerData old.layer) : NodeRow :=
  ⟨old.layer,⟨false,step.sites.layer.first,step.ownerPtr⟩,data,
    fun j=>(step.sites.ord (R.parent t (old.ord.symm j))).val⟩

private theorem prepend_recovered {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ t,Run F (R.next t)) (E : (Run.step R next).Records) (C : (Run.step R next).Charges)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool) (vis : Move.VisitPredicate F)
    (J : ∀ Pins : Type, (Run.step R next).Assembler Pins) (wordVis : ∀ Pins : Type, Run.WordVisit F Pins)
    (post : List NodeRow→Layer→Prop)
    (t : Fin R.rules.count) (hit : E.1.read (raw.take E.1.width)=some t)
    (step : R.ArchiveStep t O (C.1 t)) (head : vis R t O (C.1 t) step)
    (localWord : ∀ (Pins : Type) (L : A.Words Pins),wordVis Pins R t L ((J Pins).steps.1 L t) O (C.1 t) step) :
    Recovered (next t) (E.2 t) (C.2 t) step.sites step.data (raw.drop E.1.width) vis
      (fun Pins=>⟨(J Pins).steps.2 t⟩) wordVis
      (fun xs last=>post (interleave R t O step data :: xs) last) →
    Recovered (.step R next) E C O data raw vis J wordVis post := by
  rintro ⟨h,suffix,p,tailHit,num,seen,wordSeen,valid⟩
  refine ⟨Run.joinHistory R next t h,suffix,Run.joinArchivePath R next C O t h step p,
    Run.read_joinHistory R next E raw t hit h suffix tailHit,Run.joined_finalNumbered R next C O t h step p num,
    Run.joined_visits R next C O t h step p vis head seen,fun Pins L=>
      Run.joined_wordVisits R next (wordVis Pins) (J Pins).steps L C O t h step p (localWord Pins L)
        (wordSeen Pins ((J Pins).steps.1 L t).words),?_⟩
  rw [Run.archiveList_joinArchivePath,Run.finalArchive_layer_joinArchivePath]
  exact valid

def stagePost (K : ℕ) (ops : List Stage) (c : Cursor) (s : Layer)
    («protected» : ℕ→Prop) (mem : ℕ→ℕ) (H M : ℕ) (xs : List NodeRow) (last : Layer) : Prop :=
  NodePublication.records xs=nodeLayers K ops c s ∧ last=lastLayer K ops c s ∧
    ∀ q∈xs, ArchivedSource q «protected» mem H M

private theorem extend_stagePost {K : ℕ} {op : Stage} {ops : List Stage} {c : Cursor} {s s' : Layer}
    {«protected» : ℕ→Prop} {mem : ℕ→ℕ} {H M : ℕ} {q : NodeRow}
    (body : q.layer=s) (parent : q.parent=⟨false,(allocate K c op).next.node,(allocate K c op).words 44⟩)
    (suc : s'=nodeLayer K c op) (head : ArchivedSource q «protected» mem H M)
    {xs : List NodeRow} {last : Layer}
    (rest : stagePost K ops (allocate K c op).next s' «protected» mem H M xs last) :
    stagePost K (op::ops) c s «protected» mem H M (q::xs) last := by
  obtain ⟨rec,endLayer,res⟩:=rest
  subst s'
  refine ⟨?_,endLayer,?_⟩
  · change ⟨q.layer,q.parent⟩::NodePublication.records xs=_
    rw [rec,body,parent]
    rfl
  · intro r mem
    exact (List.mem_cons.mp mem).elim (fun e=>e.symm ▸ head) (res r)

private theorem rows_of_one_stage {d l D L u s : ℕ} {A : State d l} (R : Move F A D L)
    (t : Fin R.rules.count) (old : A.ArchiveSites) {charge : (R.next t).Site→ℕ}
    (row : R.ArchiveStep t old charge) (data : LayerData old.layer)
    {a : Archive} (op : Stage) (c : Cursor) (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    {cur ctr : Word (16*u^10)} (raw : List Bool) {out final : Memory (16*u^10)}
    (journal : a.Journal u cur ctr P rem X (allocate a.K c op).next raw out final)
    («protected» : ℕ→Prop) {H M : ℕ} (base : RowContents data «protected» (fun x=>(final x).val) H M)
    (control : cur.val<ctr.val)
    (headers : (finish a.K (op::P.directory rem (Fintype.card X.Base)) c).header≤c.heap)
    (room : (allocate a.K c op).next.heap≤cur.val)
    (range : ∀ x,c.heap≤x→x<(allocate a.K c op).next.heap→«protected» x)
    (dataRead : row.data.Reads (fun x=>(out x).val))
    (fp : row.data.Footprint (fun x=>c.heap≤x ∧ x<(allocate a.K c op).next.heap) (fun x=>(out x).val))
    (owners : ParentReads (interleave R t old row data).parent (interleave R t old row data).owners
      (fun x=>(out x).val))
    (ownerRoom : ∀ j : Fin old.layer.count,c.heap≤row.ownerPtr+j.val ∧ row.ownerPtr+j.val<(allocate a.K c op).next.heap)
    (bounds : ∀ j,(row.data.halfWidth j).length≤H ∧ (row.data.motifCopies j).length≤M) :
    RowContents row.data «protected» (fun x=>(final x).val) H M ∧
    ArchivedSource (interleave R t old row data) «protected» (fun x=>(final x).val) H M := by
  have stay (i : ℕ) (hi : c.heap≤ i ∧ i<(allocate a.K c op).next.heap) : final i=out i :=
    Archive.Journal.frame P rem X _ raw journal (ne_of_lt (hi.2.trans_le room))
      (ne_of_lt ((hi.2.trans_le room).trans control)) ⟨Or.inr (headers.trans hi.1),Or.inl hi.2⟩
  have equal (i : ℕ) (hi : c.heap≤ i ∧ i<(allocate a.K c op).next.heap) : (final i).val=(out i).val := congrArg Fin.val (stay i hi)
  refine ⟨⟨dataRead.of_footprint fp equal,(fp.transfer fp equal).mono (fun i hi=>range i hi.1 hi.2),
    fun j=>(bounds j).1,fun _ j=>(bounds j).2⟩,⟨base,?_,?_⟩⟩
  · intro nh j
    exact (equal _ (ownerRoom j)).trans (owners nh j)
  · intro _ j
    exact range _ (ownerRoom j).1 (ownerRoom j).2

structure JournalSpace (K W H M : ℕ) (ops : List Stage) (c : Cursor) (layer : Layer) (safe : ℕ→Prop) : Prop where
  nodes : ∀ q∈nodeLayers K ops c layer,q.actual.first+q.actual.count≤2^W
  header : (finish K ops c).header≤c.heap
  arena : ∀ i,c.heap≤ i→i<(finish K ops c).heap→safe i
  caps : ∀ op∈ops,stageHalves op≤H ∧ stageMotifs op≤M

private theorem JournalSpace.tail {K W H M : ℕ} {op : Stage} {ops : List Stage} {c : Cursor} {layer : Layer}
    {safe : ℕ→Prop} (space : JournalSpace K W H M (op::ops) c layer safe) :
    JournalSpace K W H M ops (allocate K c op).next (nodeLayer K c op) safe := by
  have begin : c.heap≤(allocate K c op).next.heap := by rw [heap_step];omega
  exact ⟨fun q h=>space.nodes q (List.mem_cons_of_mem _ h),space.header.trans begin,
    fun i hi=>space.arena i (begin.trans hi),fun o ho=>space.caps o (List.mem_cons_of_mem _ ho)⟩

private theorem JournalSpace.local {K W H M : ℕ} {op : Stage} {ops : List Stage} {c : Cursor} {layer : Layer}
    {safe : ℕ→Prop} (space : JournalSpace K W H M (op::ops) c layer safe) :
    (allocate K c op).next.node≤2^W ∧ ∀ i,c.heap≤ i→i<(allocate K c op).next.heap→safe i := by
  have slots := initial_fits ops (allocate K c op).next (nodeLayer K c op) space.tail.nodes
  have later : (allocate K c op).next.heap≤(finish K ops (allocate K c op).next).heap := by rw [heap_finish];omega
  refine ⟨(Nat.le_add_right _ _).trans slots,fun i lo hi=>space.arena i lo (hi.trans_le later)⟩

open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink
set_option maxRecDepth 10000 in
/-- The selected native stage outputs reconstruct a certificate on the exact record parser
and physical charge family used by the tensor contraction. Its inputs are the immutable
seed rows and the numerical address bounds of the packed finite program. -/
private theorem cursor_monotone (K : ℕ) (c : Cursor) (op : Stage) :
    c.header ≤ (allocate K c op).next.header ∧ c.dense ≤ (allocate K c op).next.dense := by
  cases op <;> constructor <;> apply Nat.le_add_right

private theorem recordedAtStage {u d l K dense : ℕ} {c : Cursor} {X : State d l}
    (op : Stage) (ops : List Stage)
    (old : OldArrayBounds dense c X)
    (headers : (finish K (op::ops) c).header ≤ dense)
    (headerStart : TickWorkspace.base u 20 ≤ c.header)
    (denseStart : dense ≤ c.dense) (width : 0 < c.width)
    (wire : X.maxWidth+1 ≤ (2^(u^10))^4) :
    RecordedArrayBounds (16*u^10) (finish K (op::ops) c).header c X := by
  have upper := headers.trans denseStart
  refine ⟨old.lower headers, ?_, upper, ?_, width, ?_⟩
  · simpa [TickWorkspace.base, TickWorkspace.stride, Nat.mul_div_cancel_left _ (by decide : 0<16)] using headerStart
  · rw [NavigationDirectory.header_finish] at upper
    simp only [List.length_cons] at upper
    omega
  · simpa only [Nat.mul_div_cancel_left _ (by decide : 0<16)] using wire


/-- The chosen program reconstructs its ordered parser, archive charges and word visits with their physical rows. -/
def WordRecoveryFor {a : Archive} {u s : ℕ} {cur ctr : Word (16*u^10)}
    (Z tariff : ℕ) («protected» : ℕ → Prop) (H MCap : ℕ) (allow : StaticMotif F → Prop)
    (P : Program F s) : Prop :=
  ∀ (bounds : ∀ b∈P.recordBounds,b.1≤a.K ∧ b.2*Z<2^(16*u^10))
    (costs : ∀ n∈P.factors,n≤tariff) {rem : ℕ} {X : State (2^s) (P.charge+rem)}
    (reach : (P.run rem X).WidthCeiling Z) (c : Cursor) (raw : List Bool)
    {input final : Memory (16*u^10)} (_journal : a.Journal u cur ctr P rem X c raw input final)
    (old : X.ArchiveSites) (_num : old.Numbered) (_first : old.layer.first=c.node) (data : LayerData old.layer)
    (_seed : RowContents data «protected» (fun i=>(final i).val) H MCap)
    (_space : JournalSpace a.K (16*u^10) H MCap (P.directory rem (Fintype.card X.Base)) c old.layer «protected»)
    (_support : P.SupportedBy allow) (_headerDense : (finish a.K (P.directory rem (Fintype.card X.Base)) c).header≤a.cursor.dense)
    (_headerStart : TickWorkspace.base u 20 ≤ c.header) (_denseStart : a.cursor.dense ≤ c.dense),
    Recovered (P.run rem X) (P.table a.K (16*u^10) Z bounds rem X reach).records
      (P.certifiedCharges tariff costs rem X).1 old data raw
      (RecordedStep a.K cur ctr (finish a.K (P.directory rem (Fintype.card X.Base)) c).header
        (finish a.K (P.directory rem (Fintype.card X.Base)) c).heap final)
      (fun Pins=>P.assembly (Pins:=Pins) rem X)
      (fun Pins=>RecordedWordStep a.K cur ctr (finish a.K (P.directory rem (Fintype.card X.Base)) c).header
        (finish a.K (P.directory rem (Fintype.card X.Base)) c).heap final Pins allow)
      (stagePost a.K (P.directory rem (Fintype.card X.Base)) c old.layer «protected» (fun i=>(final i).val) H MCap)


end
end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass
open PhysicalStage RAM.NavigationNodeRows CompressorPacking.Native.ShrinkStage
open scoped BigOperators
variable {d l : ℕ} {X : State d l} {O : X.ArchiveSites} {safe : ℕ→Prop} {m : ℕ→ℕ}

/-- The numeric stage-header tail is determined by the actual retained four-column
half rows and the selected navigation projection of their widths. -/
theorem halfRows_tail {data : LayerData O.layer} (H : State.HalfRows O safe m) (r : data.Reads m) :
    data.Tail m ∧ data.TailCells safe m := by
  classical
  let site:=fun j : Fin O.layer.count=>O.ord.symm j
  have rank (j : Fin O.layer.count) : O.ord (site j)=j := O.ord.apply_symm_apply _
  have len (j : Fin O.layer.count) : (data.halfWidth j).length=2*d :=
    (r.halves j).symm.trans (by simpa only [rank] using H.count (site j))
  have width (j : Fin O.layer.count) :
      data.halfWidth j=List.ofFn (fun i : Fin (2*d)=>X.width (Halves.sourceHalf X.graph (X.chart.symm (site j)) i)) := by
    apply List.ext_getElem (by simp only [len,List.length_ofFn])
    intro k hl hr
    have b : k<2*d := by simpa only [List.length_ofFn] using hr
    have read:=r.width j ⟨k,hl⟩
    have native:=H.width (site j) ⟨k,b⟩
    rw [rank] at native
    rw [List.getElem_ofFn]
    simpa only [Fin.getElem_fin, Fin.val_mk, Nat.add_assoc] using
      read.symm.trans (by simpa only [Nat.add_assoc] using native)
  refine ⟨?_,⟨?_,?_⟩⟩
  · intro j pos
    have p : 0<2*d := (len j) ▸ pos
    let i : Fin (2*d):=⟨2*d-1,by omega⟩
    have h:=H.start (site j) i
    have w:=H.width (site j) i
    rw [rank] at h w
    dsimp only;rw [len j]
    change m (m (O.layer.incident+j.val*2+1)+4*i.val+3)+m (m (O.layer.incident+j.val*2+1)+4*i.val+2)=_
    rw [h,w,width,List.sum_ofFn]
    exact half_tail_total p (fun k=>X.width (Halves.sourceHalf X.graph (X.chart.symm (site j)) k))
  · intro j k;simpa only [rank] using H.headerSafe (site j) k
  · intro j pos
    let k : Fin (2*d):=⟨2*d-1,by have h:=(len j) ▸ pos;omega⟩
    dsimp only;rw [len j]
    have widthCell:=H.entriesSafe (site j) k 2
    have startCell:=H.entriesSafe (site j) k 3
    rw [rank] at widthCell startCell
    exact ⟨widthCell,startCell⟩

section ReceiptTails
open Computability.VPVNP.BurstRAM
variable {F Pins : Type} [Field F] {allow : StaticMotif F → Prop} {W K headerEnd heapEnd : ℕ} {cur ctr : Word W} {final : Memory W}
    {D lanes : ℕ} {R : Move F X D lanes} {b : Fin R.rules.count}
    {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b O charge}
    {L : X.Words Pins} {ws : R.WordStep Pins L b}

/-- Retained incident fields are available for either physical stage at the same node ID. -/
theorem RecordedStep.halfRows
    (visit : RecordedStep K cur ctr headerEnd heapEnd final R b O charge row)
    (small : ∀ v,(R.next b).incidentWidth v<2^W) :
    State.HalfRows row.sites (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val) := by
  rcases visit with shrink|refresh
  · exact shrink.halfRows
  · exact refresh.halfRows small

theorem RecordedWordStep.halfRows
    (visit : RecordedWordStep K cur ctr headerEnd heapEnd final Pins allow R b L ws O charge row)
    (small : ∀ v,(R.next b).incidentWidth v<2^W) :
    State.HalfRows row.sites (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val) := by
  rcases visit with shrink|refresh
  · exact shrink.halfRows
  · exact refresh.halfRows small

theorem RecordedStep.halfTail
    (visit : RecordedStep K cur ctr headerEnd heapEnd final R b O charge row)
    (small : ∀ v,(R.next b).incidentWidth v<2^W) (read : row.data.Reads (fun i=>(final i).val)) :
    row.data.Tail (fun i=>(final i).val) ∧
      row.data.TailCells (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val) :=
  halfRows_tail (visit.halfRows small) read

theorem RecordedWordStep.halfTail
    (visit : RecordedWordStep K cur ctr headerEnd heapEnd final Pins allow R b L ws O charge row)
    (small : ∀ v,(R.next b).incidentWidth v<2^W) (read : row.data.Reads (fun i=>(final i).val)) :
    row.data.Tail (fun i=>(final i).val) ∧
      row.data.TailCells (fun i=>headerEnd≤ i ∧ i<heapEnd) (fun i=>(final i).val) :=
  halfRows_tail (visit.halfRows small) read


end ReceiptTails
end ThreeFlat.Diagonal.NavigationPass

end OAI
