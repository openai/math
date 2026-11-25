import OAI.ThreeFlat.Diagonal.TraceIterationJournal
import OAI.ThreeFlat.Diagonal.NavigationCounted
import OAI.ThreeFlat.Diagonal.NavigationStageBounds
import OAI.ThreeFlat.Diagonal.PhysicalNativeTicks

namespace OAI
/-! # Running a fixed native compressor for an arbitrary number of blocks

Each chronological step opens the selected graph, reads its own mounted histogram, and
retains its successor graph for the following step. The counted loop is permanently
installed. The repetition count and raw history are kept in separate memory words.
-/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure PhysicalStage
open CompressorPacking Native NavigationDirectory
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]
open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink

structure TraceTraversal (F : Type) [Field F] (limit W : ℕ) where
  archive : Archive
  field : FieldCode F W
  current : Word W
  counter : Word W
  stages : List Stage
  procedures : List (Procedure W)
  edges : ℕ
  capacity : ℕ
  bits : ℕ→Bool
  clock : ℕ
  prefixOK : ℕ→Prop
  journal : Memory W→Prop
  outcome : Run.WireLayer→List Bool→Prop
  limits : archive.TraceLimits limit current stages edges capacity
  word : 0<W
  room : Hierarchy.TraceRetainedRoom.Room limit W
  alphabet : archive.K≤limit
  counterHigh : current.val<counter.val

namespace TraceTraversal
variable {limit W : ℕ} (T : TraceTraversal F limit W)
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
  small : ceiling≤(limit)^4
  fixed : ∀ b∈traceWordConstants program,b≤limit
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
    ∀ final,(a).TraceJournal limit T.current T.counter program rem state (finish (a).K past (a).cursor) raw m final → T.journal final
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
  refine {here with complete:=fun final tail=>here.complete final (Archive.traceJournal_start _ _ _ _ _ (fun j hj=>by simp [writeMemory,hj]) tail), visit:=
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
    (smallZ : Z≤(limit)^4) (fixed : ∀ b∈traceWordConstants P,b≤limit)
    (past : List Stage) (idx : past.length=i) (dir : T.stages=past++(P).directory rem (Fintype.card X.Base))
    (text : T.procedures.drop i=nativeRows T.current (a).K P) (vis : (a).Visit T.stages T.edges T.bits T.current past X m)
    (time : Program.nativeTicks (a).K T.current P (finish (a).K past (a).cursor) rem (Fintype.card X.Base)≤T.clock)
    (reads : let q:=(P).table (a).K W Z bounds rem X reach
      let raw:=(List.ofFn (fun i : Fin T.capacity=>T.bits i.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ n,T.prefixOK (i+n) ↔ Run.PrefixOK n ((P).run rem X) q.records raw)
    (complete : let raw:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ final,(a).TraceJournal limit T.current T.counter P rem X (finish (a).K past (a).cursor) raw m final → T.journal final)
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
    Hierarchy.TraceShrinkRetained.onArchive T.archive G s (2^t) b (Nat.two_pow_pos _) ok B T.field T.word T.room T.current m
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
    (smallZ : Z≤(limit)^4) (fixed : ∀ b∈traceWordConstants P,b≤limit)
    (past : List Stage) (idx : past.length=i) (dir : T.stages=past++(P).directory rem (Fintype.card X.Base))
    (text : T.procedures.drop i=nativeRows T.current (a).K P) (vis : (a).Visit T.stages T.edges T.bits T.current past X m)
    (time : Program.nativeTicks (a).K T.current P (finish (a).K past (a).cursor) rem (Fintype.card X.Base)≤T.clock)
    (reads : let q:=(P).table (a).K W Z bounds rem X reach
      let raw:=(List.ofFn (fun i : Fin T.capacity=>T.bits i.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ n,T.prefixOK (i+n) ↔ Run.PrefixOK n ((P).run rem X) q.records raw)
    (complete : let raw:=(List.ofFn (fun j : Fin T.capacity=>T.bits j.val)).drop (W*((a).K*(past.map Stage.motifs).sum))
      ∀ final,(a).TraceJournal limit T.current T.counter P rem X (finish (a).K past (a).cursor) raw m final → T.journal final)
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
    Hierarchy.TraceRefreshArchivePass.onArchive T.archive G B hm hh sym rows zero conn
      T.field T.room T.word T.current m past rest T.edges T.capacity T.bits fit hb.1
      (fixed _ List.mem_cons_self) T.alphabet volume (ce.1.trans smallZ)
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
        refine ⟨m,out,fit,j,(fun _ _=>rfl),hit,dirOne,
          ⟨fixed _ List.mem_cons_self,volume,ce.1.trans smallZ,pos,control⟩,
          ⟨⟨vc.graphLow,vc.widthLow,vc.graphBound,vc.widthBound⟩,vc.stored⟩,
          published,⟨descriptors.1,descriptors.2.1,?_⟩,frame,?_⟩
        · simpa only [rest,Program.directory_length] using descriptors.2.2
        · simpa only [tailBits,pastEq,←cut] using cont
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
    refine ⟨complete m (fun _ _=>rfl),layer,(ends layer raw).mpr ?_,?_⟩
    · refine ⟨(),?_,rfl⟩
      dsimp only [raw]
      rw [bytes]
      rfl
    · change (a).Visit T.stages T.edges T.bits T.current T.stages X m
      simpa only [eq] using vis
  | shrink _ _ _ _ tail => simp [nativeRows] at text
  | refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => simp [nativeRows] at text

end TraceTraversal

theorem Archive.run_trace_repeated {limit W : ℕ} (a : Archive) (B : Block F) (n rem : ℕ)
    (X : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (field : FieldCode F W) (cur ctr : Word W) (edges cap Z : ℕ) (bits : ℕ→Bool)
    (origin : Memory W) (word : 0<W) (room : Hierarchy.TraceRetainedRoom.Room limit W) (alphabet : a.K≤limit) (counter : cur.val<ctr.val)
    (bounds : ∀ b∈(B.repeat n).recordBounds,b.1≤a.K ∧ b.2*Z<2^W)
    (reach : ((B.repeat n).run rem X).WidthCeiling Z) (small : Z≤(limit)^4)
    (fixed : ∀ b∈traceWordConstants (B.repeat n),b≤limit) :
    let P:=B.repeat n
    let steps:=P.directory rem (Fintype.card X.Base)
    let q:=P.table a.K W Z bounds rem X reach
    let raw:=List.ofFn (fun j : Fin cap=>bits j.val)
    let localSteps:=Program.nativeTicks a.K cur P a.cursor rem (Fintype.card X.Base)
    let rows:=(B.prefix (.done _)).length
    let p:=repeated cur ctr a.K B
    a.TraceLimits limit cur steps edges cap →
    TickStageSpec.Admission field p.block p.publicData
      (fun m=>m=origin ∧ a.Visit steps edges bits cur [] X m ∧ (m ctr.val).val=n)
      (fun _=>((P.run rem X).plan.read q.codes raw).isSome)
      (fun _ out=>a.TraceJournal limit cur ctr P rem X a.cursor raw origin out ∧ ∃ v : Run.WireLayer, (P.run rem X).EndsAt q.records raw v (raw.drop (W*a.histWords steps)) ∧
        a.Visit steps edges bits cur steps v.state out)
      (n*(7+(rows*(rows*localSteps)+1))+4) := by
  intro P steps q raw localSteps rows p limits
  let R:=P.run rem X
  let T : TraceTraversal F limit W :=
    { archive:=a,field:=field,current:=cur,counter:=ctr,stages:=steps,procedures:=nativeRows cur a.K P
      edges:=edges,capacity:=cap,bits:=bits,clock:=localSteps,prefixOK:=fun i=>Run.PrefixOK i R q.records raw
      journal:=a.TraceJournal limit cur ctr P rem X a.cursor raw origin,outcome:=R.EndsAt q.records raw,limits:=limits,word:=word,room:=room,alphabet:=alphabet,counterHigh:=counter }
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
  · simp [timeline,TraceTraversal.timeline,CountedTimeline.perRow,T,rows,nativeRows_length]



end
end ThreeFlat.Diagonal.NavigationPass

end OAI
