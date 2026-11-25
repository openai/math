import OAI.ThreeFlat.Diagonal.NavigationRecordedArrayBounds
import OAI.ThreeFlat.Diagonal.PhysicalNodeDirectoryCap
import OAI.ThreeFlat.Diagonal.PhysicalNodeProgram
import OAI.ThreeFlat.Diagonal.CursorSeedSites
import OAI.ThreeFlat.Diagonal.NavigationQuotaImage
import OAI.ThreeFlat.Diagonal.NavigationArchiveVisit
import OAI.ThreeFlat.Diagonal.NavigationStageBounds
import OAI.ThreeFlat.Diagonal.NavigationArchiveFields
import OAI.ThreeFlat.RAM.HistoryPhysicalFamilies
import OAI.ThreeFlat.Diagonal.TraceInitialArity
import OAI.ThreeFlat.Diagonal.TraceVolumeArithmetic
import OAI.ThreeFlat.Diagonal.PhysicalShrinkCall
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAdmission
import OAI.ThreeFlat.Diagonal.PhysicalProgramRecords
import OAI.ThreeFlat.Diagonal.TraceSeedWork
import OAI.ThreeFlat.Diagonal.NavigationArchive
import OAI.ThreeFlat.RAM.NavigationNodeRows
import OAI.ThreeFlat.RAM.TickPhysicalABI
import OAI.ThreeFlat.RAM.TickGreedyBank
import OAI.ThreeFlat.RAM.TickParameterWords
import OAI.ThreeFlat.RAM.HistoryNodeReverse
import OAI.ThreeFlat.RAM.BucketScanBoot

namespace OAI
/-! # Physical chronological archive for node records and charged work -/

namespace ThreeFlat.Diagonal.NavigationPass

open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows NavigationDirectory PhysicalStage
open scoped Classical Fin.CommRing
variable {W : ℕ}


/-- These scratch ranges lie above the exposed low physical pin arrays. The first
fourteen words of header contain scan base/length pairs, followed by the bucket ABI. -/
structure RootArchive where
  age : ℕ
  current : ℕ
  header : ℕ
  headerRaw : ℕ
  stageRaw : ℕ
  phase : ℕ
  childArena : ℕ
  sourceRows : ℕ
  groupRows : ℕ
  prefixes : ℕ
  rootCache : ℕ
  firstFinal : ℕ
  rootCount : ℕ
  initialLanes : ℕ
  pairsPerLane : ℕ
  totalPairs : ℕ
  groups : ℕ
  chunkBits : ℕ
  slotBudget : ℕ
  stageCount : ℕ
  nodeBank : Banks

open RAM.TickPhysicalABI PhysicalPinsExpr MotifRows

def RootArchive.word (a : RootArchive) : ℕ → ℕ
  | 0 => directory a.age 0 | 1 => 2*a.rootCount
  | 2 => a.prefixes | 3 => a.rootCount+1
  | 4 => 0
  | 5 => TickWorkspace.base a.age 6 | 6 => 8
  | 7 => directory a.age 3 | 8 => 3
  | 9 => a.sourceRows | 10 => 3*a.initialLanes
  | 11 => a.groupRows | 12 => 4*a.initialLanes
  | 13 => TickWorkspace.base a.age 8 | 14 => a.groups
  | 15 => TickWorkspace.base a.age 7 | 16 => a.chunkBits
  | 17 => a.sourceRows | 18 => a.groupRows | 19 => TickWorkspace.base a.age 8
  | 20 => TickWorkspace.base a.age 5 | 21 => a.sourceRows+3*a.initialLanes
  | _ => 0

def RootArchive.scan (a : RootArchive) (off : ℕ) (f : Formula 1) : Procedure W :=
  HeaderScan.procedure (a.current : Word W) off (off+1) (HeaderScan.closed f)

def RootArchive.rootCharges (a : RootArchive) : Formula 1 :=
  let i := Formula.cut (.reg 0) (.lit (directory a.age 0))
  .load (plus (.lit (a.nodeBank.charges+2*a.firstFinal)) i)

def RootArchive.prefix (a : RootArchive) : Formula 1 :=
  let i := Formula.cut (.reg 0) (.lit a.prefixes)
  let prev := Formula.cut i (.lit 1)
  .select .eq i (.lit 0) (.lit 0) (plus (.load (.cut (.reg 0) (.lit 1)))
    (.load (ix (.lit (directory a.age 0)) prev 2 0)))

def RootArchive.meta (a : RootArchive) : Formula 1 :=
  let i := Formula.cut (.reg 0) (.lit (TickWorkspace.base a.age 6))
  pick [.lit a.initialLanes,.lit a.rootCount,.load (.lit (a.prefixes+a.rootCount)),.lit (directory a.age 0),
    .lit (directory a.age 1),.lit (directory a.age 2),.lit a.stageCount,.lit (directory a.age 3)] i

/-- Initial buckets are in true cursor-zero lane order. Both endpoints are clipped so
zero-pair buckets beyond the last live pin still describe valid empty intervals. -/
def RootArchive.bucket (a : RootArchive) : Formula 1 :=
  let offset := Formula.cut (.reg 0) (.lit a.sourceRows)
  let i := Formula.op .div offset (.lit 3)
  let clipped (n : Formula 1) :=
    let t := Formula.op .mul n (.lit a.pairsPerLane)
    Formula.select .lt t (.lit a.totalPairs) t (.lit a.totalPairs)
  pick [.op .mul (.lit 4) i,clipped i,clipped (plus i (.lit 1))] (.op .mod offset (.lit 3))

def RootArchive.groupRow (a : RootArchive) : Formula 1 :=
  let offset := Formula.cut (.reg 0) (.lit a.groupRows)
  let lane := Formula.op .div offset (.lit 4)
  let root := Formula.load (plus (.lit a.rootCache) lane)
  .select .eq (.op .mod offset (.lit 4)) (.lit 0)
    (.load (ix (.lit (directory a.age 1)) root 2 0)) (.lit 0)

def RootArchive.partition (a : RootArchive) : Procedure W :=
  let area := TickWorkspace.base a.age 6
  let A : TickGreedySetup.Layout :=
    ⟨directory a.age 0,directory a.age 1,area+1,area+2,a.groups,a.totalPairs,a.slotBudget⟩
  ⟨48,17,0,TickGreedySetup.bank W A,Fin.elim0⟩

def RootArchive.ancestors (a : RootArchive) : Procedure W :=
  ⟨23,9,3,HistoryNodeDirectory.Reverse.block W,
    fun i => (![directory a.age 3,TickWorkspace.base a.age 6+1,a.rootCache] i : ℕ)⟩

def RootArchive.pack (a : RootArchive) : Procedure W :=
  let bank : ContinuationLink.Block W (10+23) 12 5 :=
    {first := (0 : Fin 10).castAdd 23
     emit := fun pc r φ exit =>
       let b := fun i : Fin 10 => pc (i.castAdd 23)
       let s := fun i : Fin 23 => pc (Fin.natAdd 10 i)
       Fin.addCases (BucketScanROM.bootEmit r φ b (s (Fin.last 22)) exit)
         (BucketScanROM.emit r s exit exit)}
  ⟨_,_,_,bank,fun i => (a.header+17+i.val : ℕ)⟩

def RootArchive.publish (a : RootArchive) : Procedure W :=
  let headerImage : PackedStageArchive.Layout := ⟨a.phase,a.headerRaw,a.headerRaw,a.header,22⟩
  let stageImage : PackedStageArchive.Layout :=
    ⟨a.phase,a.stageRaw,a.stageRaw,directory a.age 2,4*a.stageCount⟩
  let rootDesc := pick [.lit a.firstFinal,.lit a.nodeBank.nodes,.lit a.childArena]
    (.cut (.reg 0) (.lit (directory a.age 3)))
  let branches := (a.scan 0 a.rootCharges).seq ((a.scan 2 a.prefix).seq
    ((a.scan 5 a.meta).seq ((a.scan 7 rootDesc).seq (a.partition.seq a.ancestors))))
  let output := (a.scan 9 a.bucket).seq ((a.scan 11 a.groupRow).seq
    ((a.scan 13 (.lit 0)).seq ((a.scan 15 (.lit 0)).seq a.pack)))
  (PackedStageArchive.procedure headerImage).seq ((PackedStageArchive.procedure stageImage).seq
    ((start (a.current : Word W) a.header).seq (branches.seq output)))

/-- The chronological directory consumed by selected-site preparation, including the
initial cursor layer and every terminal site. Its length and each pointer are public. -/
def stageTape (rows : List Layers) : List ℕ :=
  rows.flatMap fun r => [r.actual.first,r.actual.count,r.actual.kind,r.actual.info]

@[simp] theorem stageTape_length (rows : List Layers) : (stageTape rows).length=4*rows.length := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simp [stageTape] at ih ⊢; omega

noncomputable def navigation {F : Type} [Field F] (a : Archive) (b : NodeArchive) (c : RootArchive)
    (B : Block F) (blocks residualBits finalEdges : ℕ) : Procedure W :=
  let stages := (B.repeat blocks).directory residualBits a.axes
  let rows := nodeLayers a.K stages a.cursor a.seedLayer
  (active a B blocks residualBits finalEdges).seq ((b.publish rows.length).seq c.publish)

/-- Public dimensions of a mounted diagonal tick. All compact workspaces below are
fixed disjoint regions; each scan obtains its current data from the true old/new registers. -/
structure Parameters where
  age : ℕ
  axes : ℕ
  oldAux : ℕ
  newAux : ℕ
  historyCapacity : ℕ
  rawTables : ℕ
  codebookWords : ℕ
  symbolCap : ℕ
  wireWidth : ℕ
  perLanePairs : ℕ
  totalPairs : ℕ
  traceWork : ℕ
  unitWork : ℕ
  groups : ℕ
  chunkBits : ℕ
  slotBudget : ℕ

/-- Physical parameter record at the common H/tick header. The two AUX starts are
measured after the literal cells at 0 and 1. A true paired H index occupies two complete
catalyst halves, and every trace-bearing cursor site pays for its actual seed forest. -/
noncomputable def Parameters.cursor {F : Type} [Field F] [Fintype F] (B : Block F)
    (u rem low stride cells : ℕ) (shape : RAM.PhysicalPinsExpr.Shape)
    (tableOffset unitWork : ℕ) : Parameters :=
  let k := (B.repeat (u^8)).charge+rem
  let params := 2+shape.advice+shape.teamBits+shape.timeBits
  let old := params+shape.parameterBits
  { age := u
    axes := k
    oldAux := old
    newAux := old+shape.bits
    historyCapacity := shape.bits/2
    rawTables := params+tableOffset
    codebookWords := RAM.HistoryStageBody.Physical.libraryWords B (16*u^10)
    symbolCap := B.alphabetCap
    wireWidth := 2^low*((1+((k+low)+(k+low)))*cells*3)
    perLanePairs := 2^low
    totalPairs := 2*shape.halfBits
    traceWork := TraceBitHeader.seedTraceWork low stride cells B.cursorCopies (k+low)
    unitWork := unitWork
    groups := 1024*(2*shape.chunks)
    chunkBits := shape.bits
    slotBudget := TraceVolume.cap u/4 }

/-- Bounds on the actual packed scratch regions, independent of the guessed history. -/
structure Archive.Limits (a : Archive) (u : ℕ) (cur : Word (16*u^10))
    (steps : List Stage) (edges cap : ℕ) : Prop where
  origin : a.cursor.header=a.seed+64
  tables : a.seed+(a.directory steps edges (16*u^10)).length≤a.cursor.dense
  raw : a.cursor.dense+a.histWords steps≤a.cursor.heap
  controls : a.cursor.heap+(steps.map Stage.heapWords).sum≤cur.val
  volume : (steps.map Stage.heapWords).sum≤2^(u^10)
  capacity : (16*u^10)*a.histWords steps≤cap

/-- The numerical preconditions of every local native call, derived from a single trim
of the actual full navigation directory into past, current and future stages. -/
theorem Archive.Limits.at_step {a : Archive} {u edges cap : ℕ} {cur : Word (16*u^10)}
    {pre post : List Stage} {step : Stage} (all : a.Limits u cur (pre++step::post) edges cap) :
    let c:=finish a.K pre a.cursor
    let steps:=pre++step::post
    a.cursor.dense+a.histWords steps≤c.heap ∧ c.header+64≤a.cursor.dense ∧
      (allocate a.K c step).next.heap≤cur.val ∧ step.heapWords≤2^(u^10) ∧
      (16*u^10)*(a.K*(pre.map Stage.motifs).sum)+step.motifs*a.K*(16*u^10)≤cap := by
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
  have bytes := (Nat.mul_le_mul_left (16*u^10) cells).trans capacity
  rw [Nat.mul_add,Nat.mul_comm (16*u^10) (step.motifs*a.K)] at bytes
  exact ⟨dense.trans before,by omega,bound,by omega,bytes⟩

theorem RecordedArrayBounds.header20_at {u head d l : ℕ} {c : Cursor} {X : State d l}
    (a : RecordedArrayBounds (16*u^10) head c X) : TickWorkspace.base u 20 ≤ c.header := by
  simpa [TickWorkspace.base,TickWorkspace.stride,Nat.mul_div_cancel_left _ (by decide : 0<16)] using a.headerLow

theorem RecordedArrayBounds.header_at {u head d l : ℕ} {c : Cursor} {X : State d l}
    (a : RecordedArrayBounds (16*u^10) head c X) : TickWorkspace.base u 19 ≤ c.header := by
  have h:=a.header20_at
  change 21*TickWorkspace.stride u≤c.header at h
  change 20*TickWorkspace.stride u≤c.header
  omega

theorem RecordedArrayBounds.wire_at {u head d l : ℕ} {c : Cursor} {X : State d l}
    (a : RecordedArrayBounds (16*u^10) head c X) : X.maxWidth+1 ≤ (2^(u^10))^4 := by
  simpa only [Nat.mul_div_cancel_left _ (by decide : 0<16)] using a.wire

section ShrinkPass
open Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink
open scoped Classical
variable {F : Type} [Field F] {u : ℕ} (a : Archive) (T : ShrinkMotif.Table F) (s D rem : ℕ)
    (hD : 0<D) (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024)
    (A : State (2^s) (shrinkCharge s+rem))
local notation "W₀" => 16*u^10
local notation "d" => (2^s:ℕ)
local notation "N" => Fintype.card (State.Base (shrinkRecordState s rem A))
local notation "x" => dims (shrinkStage s D) N (CompressorPacking.tagBits d) rem
local notation "step" => Stage.shrink x
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A

/-- The actual native shrinking call on a chronological archive chooses the canonical next
history branch and leaves the exact resident graph for either type of following instruction. -/
theorem shrink_on_archive (field : FieldCode F W₀) (hu : 40≤u) (cur : Word W₀) (m₀ : Memory W₀)
    (pre post : List Stage) (edges cap : ℕ) (raw : ℕ→Bool)
    (fit : (Q).Fits a.K W₀) (alphabet : shrinkSymbolBound T≤a.K)
    (fixed : shrinkFixedWords T s D≤u) (arena : (step).heapWords≤2^(u^10))
    (wire : A.maxWidth+1≤(2^(u^10))^4) :
    let steps:=pre++step::post
    let c:=finish a.K pre a.cursor
    let entry:=allocate a.K c step
    let rawBits:=(List.ofFn (fun i : Fin cap=>raw i.val)).drop (W₀*(a.K*(pre.map Stage.motifs).sum))
    a.Live steps edges raw cur c m₀ → a.cursor.header=a.seed+64 →
    a.seed+(a.directory steps edges W₀).length≤a.cursor.dense →
    a.cursor.dense+a.histWords steps≤c.heap → c.header+64≤a.cursor.dense →
    c.header+64≤c.graph → c.header+64≤c.width →
    c.graph+6*(x).oldEdges≤c.heap → c.width+(x).oldEdges*(x).originalLanes≤c.heap →
    entry.next.heap≤cur.val → W₀*(a.K*(pre.map Stage.motifs).sum)+(Q).motifs*a.K*W₀≤cap →
    SlotImage.Stored A.graph A.order (tagOrdinal _) (RefreshStageNav.oldColumns c (Fintype.card A.Base) d)
      (fun i=>(m₀ i).val) A.width →
    let body:=NavigationPass.shrink cur a.K s D T
    TickStageSpec.Admission field body.block body.publicData (fun m=>m=m₀)
      (fun _=>(((Q).record fit).read (rawBits.take ((Q).record fit).width)).isSome)
      (fun _ out=>∃ j : Fin (M).rules.count,((Q).record fit).read (rawBits.take ((Q).record fit).width)=some j ∧
        a.Live steps edges raw cur entry.next out ∧
        SlotImage.Stored ((M).next j).graph ((M).next j).order (tagOrdinal rem)
          (RefreshStageNav.oldColumns entry.next (Fintype.card ((M).next j).Base) D)
          (fun i=>(out i).val) ((M).next j).width ∧
        ShrinkOutput (K:=a.K) T s D rem hD small A cur m₀ c j out)
      (shrinkBudget T s D rem hD small A a.K cur c) := by
  intro steps c entry rawBits live origin table dense later nextGraph nextWidth graph widths ctrl capRoom old body
  have bump : c.heap≤entry.next.heap := by dsimp only [entry];rw [heap_step];omega
  have high : c.heap≤cur.val := bump.trans ctrl
  have static : a.seed+(a.directory steps edges W₀).length≤c.heap := table.trans (by omega)
  have tableFit : a.seed+(a.directory steps edges W₀).length<2^W₀ := static.trans_lt (high.trans_lt cur.isLt)
  have widthCount : (Q).motifs=(step).motifs := by
    rw [shrinkBinaryFamily_motifs]
    change Fintype.card A.Base*_ * _ * _ * _ * _=N*_ * _ * _ * _ * _
    rw [shrink_record_base s rem A]
    rfl
  have locals := live.input Q widthCount fit cap capRoom
  let digit:=RawHistogram.stage (W:=W₀) (Q).motifs a.K raw (a.K*(pre.map Stage.motifs).sum)
  have head : rawBits.take ((Q).record fit).width=List.ofFn (HistogramRegister.bitTable digit) := locals.2
  have counts : c.dense+a.K*(step).motifs≤c.heap := by
    apply le_trans _ dense
    dsimp only [c,steps,Archive.histWords]
    rw [dense_finish]
    simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons,Nat.mul_add]
    omega
  let here : CursorSpace cur m₀ c a.K x :=
    ⟨live.header origin tableFit, graph,widths,counts,later.trans (by omega),ctrl⟩
  intro np nr nk machine pc reg pub exit inst data config mem atPc initial
  obtain ⟨accept,reject⟩ := shrink_at_scale T s D rem hD small A hu field cur m₀ c here
    ⟨nextGraph,nextWidth⟩ old fit digit locals.1 fixed alphabet arena wire
    machine pc reg pub exit inst data config mem atPc initial
  constructor
  · intro valid
    obtain ⟨ticks,bounded,result,out,atExit,⟨j,parse,published⟩,run⟩:=accept (by rwa [head] at valid)
    refine ⟨ticks,bounded,result,out,atExit,?_,run⟩
    refine ⟨j,(by simpa only [head] using parse),live.advance step published.pointer static dense later high
      (fun i hc hsel low=>published.archive i hc hsel (.inl low)),?_,published⟩
    rw [←shrink_output_columns T s D rem hD small A a.K c j]
    exact published.stored
  · intro invalid
    exact reject (by rwa [head] at invalid)

end ShrinkPass

section RefreshPass
open Computability.VPVNP.Compression CompressorPacking Native RefreshDemandRows RefreshTies RefreshStageNav
open scoped Classical BigOperators
variable {F : Type} [Field F] {u s rem h pad : ℕ} {g : Fin (2^s)→Fin (2^s)→ℕ} {C γ : ℝ}
    (a : Archive) (T : RefreshMotif.Table F g (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,g i j=g j i) (rows : ∀ i,∑ j,g i j=h)
    (zero : ∀ i,g i i=0) (conn : Expander.Bound (Expander.transition g h) ℝ γ)
local notation "W₀" => 16*u^10
local notation "d" => 2^s
local notation "v" => Fintype.card A.Base
local notation "step" => Stage.refresh v d (2^rem) h pad
local notation "M" => refreshBinary T A hm hh sym rows zero conn
local notation "Q" => refreshBinaryFamily T A hm hh sym rows zero conn

theorem refresh_on_archive (field : FieldCode F W₀) (hu : 40≤u) (cur : Word W₀) (m₀ : Memory W₀)
    (pre post : List Stage) (edges cap : ℕ) (raw : ℕ→Bool) (fit : (Q).Fits a.K W₀)
    (alphabet : refreshSymbolBound T≤a.K) (fixed : refreshFixedWords T≤u) (count : a.K≤u)
    (arena : (step).heapWords≤2^(u^10)) (wire : A.maxWidth+1≤(2^(u^10))^4) :
    let steps:=pre++step::post
    let c:=finish a.K pre a.cursor
    let entry:=allocate a.K c step
    let rawBits:=(List.ofFn (fun i : Fin cap=>raw i.val)).drop (W₀*(a.K*(pre.map Stage.motifs).sum))
    a.Live steps edges raw cur c m₀ → a.cursor.header=a.seed+64 →
    a.seed+(a.directory steps edges W₀).length≤a.cursor.dense →
    a.cursor.dense+a.histWords steps≤c.heap → c.header+64≤a.cursor.dense →
    c.graph+6*(v*d)≤c.heap → c.width+v*d*(d*2^rem)≤c.heap →
    entry.next.heap≤cur.val → W₀*(a.K*(pre.map Stage.motifs).sum)+(Q).motifs*a.K*W₀≤cap →
    SlotImage.Stored A.graph A.order (tagOrdinal _) (oldColumns c v d) (fun i=>(m₀ i).val) A.width →
    let body:=NavigationPass.refresh cur a.K s h pad T sym rows zero
    let middle:=((refreshPre T cur).pipeline cur).run m₀
    TickStageSpec.Admission field body.block body.publicData (fun m=>m=m₀)
      (fun _=>(((Q).record fit).read (rawBits.take ((Q).record fit).width)).isSome)
      (fun _ out=>∃ j : Fin (M).rules.count,((Q).record fit).read (rawBits.take ((Q).record fit).width)=some j ∧
        a.Live steps edges raw cur entry.next out ∧
        SlotImage.Stored ((M).next j).graph ((M).next j).order (tagOrdinal rem)
          (oldColumns entry.next (Fintype.card ((M).next j).Base) (1+h+pad))
          (fun i=>(out i).val) ((M).next j).width ∧
        RefreshOutput T A hm hh sym rows zero conn a.K cur c j middle out ∧
        ((∀ (i : Fin (Q).motifs) (f : Fin 3),out (c.heap+(i.val*3+f.val))=
          ((if f.val=0 then (Q).copies i else if f.val=1 then
            (T.winner (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A)
              ((refreshBlockOrder A).symm i)).val else Fintype.card ((Q).alphabet i):ℕ):Word W₀)) ∧
          QuotaImage Q fit j c out ∧ c.header+64*(post.length+1)≤c.dense) ∧
        ∀ k,k≠cur.val → (k<c.heap ∨ entry.next.heap≤k) → out k=m₀ k)
      (refreshCallTime T A sym rows zero a.K cur c) := by
  intro steps c entry rawBits live origin table dense later graph widths ctrl capRoom old body middle
  have bump : c.heap≤entry.next.heap := by dsimp only [entry];rw [heap_step];omega
  have high : c.heap≤cur.val := bump.trans ctrl
  have static : a.seed+(a.directory steps edges W₀).length≤c.heap := table.trans (by omega)
  have tableFit : a.seed+(a.directory steps edges W₀).length<2^W₀ := static.trans_lt (high.trans_lt cur.isLt)
  have locals := live.input Q (by rfl) fit cap capRoom
  let digit:=RawHistogram.stage (W:=W₀) (Q).motifs a.K raw (a.K*(pre.map Stage.motifs).sum)
  have head : rawBits.take ((Q).record fit).width=List.ofFn (HistogramRegister.bitTable digit) := locals.2
  have counts : c.dense+a.K*(step).motifs≤c.heap := by
    apply le_trans _ dense
    dsimp only [c,steps,Archive.histWords]
    rw [dense_finish]
    simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons,Nat.mul_add]
    omega
  let here : RefreshStageNav.CursorSpace cur m₀ c a.K v s rem h pad :=
    ⟨live.header origin tableFit,graph,widths,by simpa [Stage.motifs,RefreshStageLayout.counts,Nat.mul_comm] using counts,
      later.trans (by omega),ctrl⟩
  obtain ⟨vb,lb,db,sb,rom,rot,full,tiles,kf,wb,top⟩:=refresh_scalar_room T A hu fixed count arena wire
  have positive : 0<W₀ :=
    Nat.mul_pos (by decide : 0 < 16) (pow_pos (by omega : 0 < u) 10)
  intro np nr nk machine pc reg pub exit inst data config mem atPc initial
  obtain ⟨accept,reject⟩:=refresh_admission T A hm hh sym rows zero conn field positive cur m₀ c here old fit digit
    (fun i j=>by simpa only [Nat.mul_comm a.K i.val] using locals.1 i j) vb lb db sb rom rot full tiles
    alphabet kf wb top machine pc reg pub exit inst data config mem atPc initial
  constructor
  · intro valid
    obtain ⟨ticks,bounded,result,out,atExit,⟨j,parse,published,words,fr⟩,run⟩:=accept (by rwa [head] at valid)
    refine ⟨ticks,bounded,result,out,atExit,?_,run⟩
    have chosen : HistogramRegister.words ((Q).rows fit) ((Q).sequence fit j)=digit :=
      HistogramRegister.bitTable.injective (List.ofFn_inj.mp (((Q).record fit).write_read _ _ parse))
    have capRows : c.dense+a.K*(Q).motifs≤c.heap:=counts
    have qimage : QuotaImage Q fit j c out:=by
      refine ⟨capRows,?_⟩
      intro i l
      have a₁:=Nat.mul_le_mul_left a.K i.isLt
      rw [Nat.mul_succ] at a₁
      have a₂:=l.isLt
      rw [fr _ (by omega) (.inl (by omega)),chosen];exact locals.1 i l
    have floor : c.header+64*(post.length+1)≤c.dense:=by
      dsimp only [c]
      rw [header_finish,dense_finish,origin]
      rw [Archive.directory_length] at table
      dsimp only [steps] at table
      simp only [List.length_append,List.length_cons] at table
      omega
    refine ⟨j,(by simpa only [head] using parse),live.advance step published.pointer static dense later high
      (fun i hc _ low=>fr i hc (.inl low)),?_,published,⟨words,qimage,floor⟩,fr⟩
    have stored:=published.graph
    have columns : oldColumns entry.next (Fintype.card ((M).next j).Base) (1+h+pad)=
        nextColumns entry v d h pad := by
      exact congrArg (fun b=>oldColumns entry.next b (1+h+pad))
        (refreshBinary_next_base T A hm hh sym rows zero conn j)
    rw [columns]
    exact stored
  · intro invalid
    exact reject (by rwa [head] at invalid)


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The physically selected, degree-recast refresh move and its exact navigation banks.
The immutable output contains the children, widths, repeat counts, and predecessor owners. -/
theorem refresh_archive_step_at_scale {K tariff D : ℕ} (deg : 1+h+pad=D)
    (c : Cursor) (cur : Word W₀) (branch : Fin (M).rules.count) (prepared out : Memory W₀)
    (result : RefreshOutput T A hm hh sym rows zero conn K cur c branch prepared out) (fit : (Q).Fits K W₀)
    (copies : ∀ i : Fin (Q).motifs,out (c.heap+i.val*3)=((Q).copies i : Word W₀))
    (heap : (allocate K c step).next.heap≤2^W₀) (ids : c.node+v*d*2^rem≤2^W₀)
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=c.node)
    (chargeBound : ∀ b,(∑ y,refreshBinaryCharge T A hm hh sym rows zero conn b y)≤
      tariff*(A.positions+A.widthSum+((M).next b).positions+((M).next b).widthSum)) :
    let R:=Program.recastMove deg M
    let b:=Program.degreeTerm deg M branch
    let funding : Program.siteCharge M tariff:=⟨refreshBinaryCharge T A hm hh sym rows zero conn,chargeBound⟩
    ∃ Rstep : R.ArchiveStep b old ((Program.siteRecast deg M funding).1 b),
      let en:=allocate K c step
      let mem:=fun i=>(out i).val
      let owner:=fun j:Fin old.layer.count=>(Rstep.sites.ord (R.parent b (old.ord.symm j))).val
      Rstep.sites.Numbered ∧ Rstep.sites.layer=nodeLayer K c step ∧ Rstep.ownerPtr=en.words 44 ∧
      Rstep.data.Reads mem ∧ Rstep.data.Below en.next.heap mem ∧
      Rstep.data.Footprint (fun i=>c.heap ≤ i ∧ i<en.next.heap) mem ∧
      ParentReads ⟨false,Rstep.sites.layer.first,Rstep.ownerPtr⟩ owner mem ∧
      (∀ j : Fin old.layer.count,c.heap≤Rstep.ownerPtr+j.val ∧ Rstep.ownerPtr+j.val<en.next.heap) ∧
      (∀ j,(Rstep.data.halfWidth j).length≤ stageHalves step ∧
        (Rstep.data.motifCopies j).length≤ stageMotifs step) ∧
      Rstep=Program.recastArchiveStep deg M funding branch old
        (refreshArchiveStep T A hm hh sym rows zero conn result fit copies old numbered first) := by
  cases deg
  let data:=refreshArchiveStep T A hm hh sym rows zero conn result fit copies old numbered first
  let funding : Program.siteCharge M tariff:=⟨refreshBinaryCharge T A hm hh sym rows zero conn,chargeBound⟩
  refine ⟨Program.recastArchiveStep rfl M funding branch old data,?_,rfl,rfl,?_⟩
  · exact refreshArchiveSites_numbered T A hm hh sym rows zero conn K c branch
  obtain ⟨reads,below,foot⟩:=RefreshOutput.archiveWithFootprint T A hm hh sym rows zero conn result heap ids
  refine ⟨reads,below,foot,?_,?_,?_,rfl⟩
  · exact refreshArchive_parentReads T A hm hh sym rows zero conn result old numbered (by omega)
  · exact refreshArchive_ownerFootprint (A:=A) (K:=K) (h:=h) (pad:=pad) c old
  · intro j
    constructor
    · change (List.ofFn (fun q : Fin (2*(1+h+pad))=>_)).length≤2*(1+h+pad)
      simp only [List.length_ofFn,le_refl]
    · exact le_rfl

end RefreshPass

section RefreshJournal
open Computability.VPVNP.Compression CompressorPacking Native RefreshDemandRows RefreshTies RefreshStageNav
open scoped BigOperators Classical Fin.CommRing
noncomputable section

/-- Every quantity needed to re-read an actual H stage, prior to the output-degree cast.
The middle memory is obtained by the native preparation program itself. -/
structure RefreshReceipt (F : Type) [Field F] {W : ℕ} (K : ℕ) (cur : Word W) where
  s : ℕ
  rem : ℕ
  h : ℕ
  pad : ℕ
  degree : ℕ
  tariff : ℕ
  mult : Fin (2^s)→Fin (2^s)→ℕ
  gridConstant : ℝ
  gap : ℝ
  tile : RefreshMotif.Table F mult (1+h+pad) gridConstant
  input : State (2^s) (s+rem)
  hm : 2≤2^s
  hh : 0<h
  sym : ∀ i j,mult i j=mult j i
  rowSum : ∀ i,∑ j,mult i j=h
  noLoop : ∀ i,mult i i=0
  conn : Expander.Bound (Expander.transition mult h) ℝ gap
  degreeEq : 1+h+pad=degree
  cursor : Cursor
  mid : Memory W
  out : Memory W
  branch : Fin (refreshBinary tile input hm hh sym rowSum noLoop conn).rules.count
  fit : (refreshBinaryFamily tile input hm hh sym rowSum noLoop conn).Fits K W
  old : input.ArchiveSites
  numbered : old.Numbered
  first : old.layer.first=cursor.node
  stored : SlotImage.Stored input.graph input.order (tagOrdinal (s+rem))
    (RefreshStageNav.oldColumns cursor (Fintype.card input.Base) (2^s)) (fun i=>(mid i).val) input.width
  issued : RefreshOutput tile input hm hh sym rowSum noLoop conn K cur cursor branch
    (((refreshPre tile cur).pipeline cur).run mid) out
  published : let Q:=refreshBinaryFamily tile input hm hh sym rowSum noLoop conn
    ∀ (i : Fin Q.motifs) (f : Fin 3),out (cursor.heap+(i.val*3+f.val))=
      ((if f.val=0 then Q.copies i else if f.val=1 then
        (tile.winner (refreshBinaryGraph input) (tagOrdinal s).symm (refreshBinaryInput input)
          ((refreshBlockOrder input).symm i)).val else Fintype.card (Q.alphabet i):ℕ):Word W)
  histogram : QuotaImage (refreshBinaryFamily tile input hm hh sym rowSum noLoop conn) fit branch cursor out
  chargeBound : let R:=refreshBinary tile input hm hh sym rowSum noLoop conn
    ∀ b,(∑ y,refreshBinaryCharge tile input hm hh sym rowSum noLoop conn b y)≤
      tariff*(input.positions+input.widthSum+(R.next b).positions+(R.next b).widthSum)

namespace RefreshReceipt
variable {F : Type} [Field F] {W K : ℕ} {cur : Word W} (q : RefreshReceipt F K cur)
local notation "M" => refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn
local notation "Q" => refreshBinaryFamily q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn

def entry := allocate K q.cursor (.refresh (Fintype.card q.input.Base) (2^q.s) (2^q.rem) q.h q.pad)
def funding : Program.siteCharge M q.tariff :=
  ⟨refreshBinaryCharge q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn,q.chargeBound⟩
def move := Program.recastMove q.degreeEq M
def term := Program.degreeTerm q.degreeEq M q.branch
def charge := (Program.siteRecast q.degreeEq M q.funding).1 q.term

def step : q.move.ArchiveStep q.term q.old q.charge :=
  Program.recastArchiveStep q.degreeEq M q.funding q.branch q.old
    (refreshArchiveStep q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.issued q.fit
      (fun i=>by simpa using q.published i 0) q.old q.numbered q.first)
end RefreshReceipt

private theorem archiveHalfRows_cast {F : Type} [Field F] {i l D D' l' h W : ℕ} {B : State i l}
    (deg : D=D') (M : Move F B D l') (cost : Program.siteCharge M h) (j : Fin M.rules.count)
    (old : B.ArchiveSites) (row : M.ArchiveStep j old (cost.1 j)) (safe : ℕ→Prop) (mem : ℕ→ℕ)
    (raw : (∀ y,(M.next j).incidentWidth y<2^W)→State.HalfRows row.sites safe mem) :
    (∀ y,((Program.recastMove deg M).next (Program.degreeTerm deg M j)).incidentWidth y<2^W)→
      State.HalfRows (Program.recastArchiveStep deg M cost j old row).sites safe mem := by
  cases deg
  exact raw

theorem RefreshReceipt.halfRows {F : Type} [Field F] {W K hEnd eEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} (q : RefreshReceipt F K cur) (limit : q.entry.next.heap≤eEnd)
    (frame : SavedFrame cur ctr hEnd q.entry.next.header q.entry.next.heap q.out final)
    (bounds : hEnd≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val) :
    (∀ y,(q.move.next q.term).incidentWidth y<2^W)→
      State.HalfRows q.step.sites (fun i=>hEnd ≤ i ∧ i<eEnd) (fun i=>(final i).val) := by
  apply archiveHalfRows_cast
  intro small
  have localRows:=RefreshOutput.halfRows q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn
    q.issued (bounds.2.1.trans cur.isLt.le) small
  apply localRows.transfer
  · intro x region
    have beforeCursor : x < cur.val := lt_of_lt_of_le region.2 bounds.2.1
    exact congrArg Fin.val (frame x beforeCursor.ne (beforeCursor.trans bounds.2.2).ne
      (.inr (bounds.1.trans region.1)) region.2)
  · intro x region
    exact ⟨bounds.1.trans region.1,region.2.trans_le limit⟩

/-- The dense histogram is above the complete chronological header bank. -/
structure RefreshBounds (headerEnd heap nextHeap dense cur ctr:ℕ) : Prop where
  header : headerEnd≤heap
  controls : nextHeap≤cur ∧ cur<ctr
  quota : headerEnd≤dense

/-- A receipt is carried by precisely the admitted move, branch, numbering and
row. The frame keeps its actual outputs accessible in the final memory. -/
inductive RefreshVisit {F : Type} [Field F] {W : ℕ} (K : ℕ) (cur ctr : Word W)
    (headerEnd heapEnd : ℕ) (final : Memory W) : Move.VisitPredicate F where
  | native (q : RefreshReceipt F K cur) (limit : q.entry.next.heap≤heapEnd)
      (frame : SavedFrame cur ctr headerEnd q.entry.next.header q.entry.next.heap q.out final)
      (bounds : RefreshBounds headerEnd q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
      (oldArrays : RecordedArrayBounds W headerEnd q.cursor q.input) :
      RefreshVisit K cur ctr headerEnd heapEnd final q.move q.term q.old q.charge q.step

theorem RefreshVisit.transfer {F : Type} [Field F] {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {before after : Memory W} {d l D L : ℕ} {X : State d l} {R : Move F X D L}
    {b : Fin R.rules.count} {old : X.ArchiveSites} {f : (R.next b).Site→ℕ} {step : R.ArchiveStep b old f}
    (visit : RefreshVisit K cur ctr headerEnd heapEnd before R b old f step)
    (same : ∀ i,i<heapEnd→after i=before i) :
    RefreshVisit K cur ctr headerEnd heapEnd after R b old f step := by
  cases visit with
  | native q limit frame bounds oldArrays => exact .native q limit (frame.transfer limit same) bounds oldArrays

theorem RefreshVisit.halfRows {F : Type} [Field F] {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} {d l D m : ℕ} {A : State d l} {R : Move F A D m}
    {b : Fin R.rules.count} {old : A.ArchiveSites} {f : (R.next b).Site→ℕ} {row : R.ArchiveStep b old f}
    (r : RefreshVisit K cur ctr headerEnd heapEnd final R b old f row)
    (small : ∀ z,(R.next b).incidentWidth z<2^W) :
    State.HalfRows row.sites (fun i=>headerEnd ≤ i ∧ i<heapEnd) (fun i=>(final i).val) := by
  cases r with
  | native q limit frame bounds oldArrays => exact q.halfRows limit frame ⟨bounds.header,bounds.controls⟩ small

/-- The literal word assembler used by the physical program on the issued receipt. -/
def RefreshReceipt.wordStep {F Pins : Type} [Field F] {W K : ℕ} {cur : Word W}
    (q : RefreshReceipt F K cur) (L : q.input.Words Pins) : q.move.WordStep Pins L q.term :=
  Move.outputAssembler q.degreeEq
    (refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn)
    (refreshBinary_assembler q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn) L q.term

/-- The physical archive row and word assembler refer to a single refresh receipt. -/
inductive RefreshWordVisit {F Pins : Type} [Field F] {W : ℕ} (K : ℕ) (cur ctr : Word W)
    (headerEnd heapEnd : ℕ) (final : Memory W) (allow : StaticMotif F→Prop) : Run.WordVisit F Pins where
  | native (q : RefreshReceipt F K cur) (limit : q.entry.next.heap≤heapEnd)
      (frame : SavedFrame cur ctr headerEnd q.entry.next.header q.entry.next.heap q.out final)
      (bounds : RefreshBounds headerEnd q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
      (oldArrays : RecordedArrayBounds W headerEnd q.cursor q.input)
      (L : q.input.Words Pins) (permitted : allow (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile)) :
      RefreshWordVisit K cur ctr headerEnd heapEnd final allow q.move q.term L (q.wordStep L) q.old q.charge q.step

namespace RefreshWordVisit
variable {F Pins : Type} [Field F] {allow : StaticMotif F→Prop} {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {before after : Memory W} {d l D m : ℕ} {A : State d l} {R : Move F A D m}
    {i : Fin R.rules.count} {L : A.Words Pins} {ws : R.WordStep Pins L i}
    {old : A.ArchiveSites} {f : (R.next i).Site→ℕ} {row : R.ArchiveStep i old f}

theorem transfer (r : RefreshWordVisit K cur ctr headerEnd heapEnd before allow R i L ws old f row)
    (same : ∀ x,x<heapEnd→after x=before x) :
    RefreshWordVisit K cur ctr headerEnd heapEnd after allow R i L ws old f row := by
  cases r with
  | native q limit frame bounds oldArrays words permitted => exact .native q limit (frame.transfer limit same) bounds oldArrays words permitted

theorem visit (r : RefreshWordVisit K cur ctr headerEnd heapEnd before allow R i L ws old f row) :
    RefreshVisit K cur ctr headerEnd heapEnd before R i old f row := by
  cases r with
  | native q limit frame bounds oldArrays words permitted => exact .native q limit frame bounds oldArrays

theorem halfRows (r : RefreshWordVisit K cur ctr headerEnd heapEnd before allow R i L ws old f row)
    (small : ∀ z,(R.next i).incidentWidth z<2^W) :
    State.HalfRows row.sites (fun j=>headerEnd≤j ∧ j<heapEnd) (fun j=>(before j).val) :=
  r.visit.halfRows small

theorem childOrder (r : RefreshWordVisit K cur ctr headerEnd heapEnd before allow R i L ws old f row) :
    ws.ChildOrder row := by
  cases r with
  | native q limit frame bounds oldArrays words permitted =>
    exact refresh_childOrder_at_scale q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn
      q.degreeEq words (q.wordStep words) q.step

end RefreshWordVisit

section Constructor
variable {F : Type} [Field F] {W s rem h pad K : ℕ} {g : Fin (2^s)→Fin (2^s)→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F g (1+h+pad) C) (A : State (2^s) (s+rem))
  (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,g i j=g j i) (rows : ∀ i,∑ j,g i j=h)
  (zero : ∀ i,g i i=0) (conn : Expander.Bound (Expander.transition g h) ℝ γ)
local notation "M" => refreshBinary T A hm hh sym rows zero conn
local notation "Q" => refreshBinaryFamily T A hm hh sym rows zero conn
local notation "op" => Stage.refresh (Fintype.card A.Base) (2^s) (2^rem) h pad

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem RefreshVisit.of_native {D tariff : ℕ} (degreeEq : 1+h+pad=D) (c : Cursor) (cur ctr : Word W)
    (headerEnd heapEnd : ℕ) (branch : Fin (M).rules.count) (mid out final : Memory W)
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=c.node)
    (stored : SlotImage.Stored A.graph A.order (tagOrdinal (s+rem))
      (RefreshStageNav.oldColumns c (Fintype.card A.Base) (2^s)) (fun i=>(mid i).val) A.width)
    (oldArrays : RecordedArrayBounds W headerEnd c A)
    (actual : RefreshOutput T A hm hh sym rows zero conn K cur c branch (((refreshPre T cur).pipeline cur).run mid) out)
    (fit : (Q).Fits K W) (published : ∀ (i : Fin (Q).motifs) (f : Fin 3),out (c.heap+(i.val*3+f.val))=
      ((if f.val=0 then (Q).copies i else if f.val=1 then
        (T.winner (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A)
          ((refreshBlockOrder A).symm i)).val else Fintype.card ((Q).alphabet i):ℕ):Word W))
    (histogram : QuotaImage Q fit branch c out) (fund : ∀ b,(∑ y,refreshBinaryCharge T A hm hh sym rows zero conn b y)≤
      tariff*(A.positions+A.widthSum+((M).next b).positions+((M).next b).widthSum))
    (limit : (allocate K c op).next.heap≤heapEnd)
    (frame : SavedFrame cur ctr headerEnd (allocate K c op).next.header (allocate K c op).next.heap out final)
    (bounds : RefreshBounds headerEnd c.heap (allocate K c op).next.heap c.dense cur.val ctr.val) :
    let R:=Program.recastMove degreeEq M
    let b:=Program.degreeTerm degreeEq M branch
    let funding : Program.siteCharge M tariff:=⟨refreshBinaryCharge T A hm hh sym rows zero conn,fund⟩
    let f:=(Program.siteRecast degreeEq M funding).1 b
    ∀ (s₀ : R.ArchiveStep b old f),s₀=Program.recastArchiveStep degreeEq M funding branch old
      (refreshArchiveStep T A hm hh sym rows zero conn actual fit (fun i=>by simpa using published i 0)
        old numbered first) → RefreshVisit K cur ctr headerEnd heapEnd final R b old f s₀ := by
  let q : RefreshReceipt F K cur := ⟨s,rem,h,pad,D,tariff,g,C,γ,T,A,hm,hh,sym,rows,zero,conn,
    degreeEq,c,mid,out,branch,fit,old,numbered,first,stored,actual,published,histogram,fund⟩
  intro R b funding f s₀ eq
  subst s₀
  exact .native q limit frame bounds oldArrays

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem RefreshWordVisit.of_native {Pins : Type} {allow : StaticMotif F→Prop} {D tariff : ℕ} (degreeEq : 1+h+pad=D) (c : Cursor) (cur ctr : Word W)
    (headerEnd heapEnd : ℕ) (branch : Fin (M).rules.count) (mid out final : Memory W)
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=c.node)
    (stored : SlotImage.Stored A.graph A.order (tagOrdinal (s+rem))
      (RefreshStageNav.oldColumns c (Fintype.card A.Base) (2^s)) (fun i=>(mid i).val) A.width)
    (oldArrays : RecordedArrayBounds W headerEnd c A)
    (actual : RefreshOutput T A hm hh sym rows zero conn K cur c branch (((refreshPre T cur).pipeline cur).run mid) out)
    (fit : (Q).Fits K W) (published : ∀ (i : Fin (Q).motifs) (f : Fin 3),out (c.heap+(i.val*3+f.val))=
      ((if f.val=0 then (Q).copies i else if f.val=1 then
        (T.winner (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A)
          ((refreshBlockOrder A).symm i)).val else Fintype.card ((Q).alphabet i):ℕ):Word W))
    (histogram : QuotaImage Q fit branch c out) (fund : ∀ b,(∑ y,refreshBinaryCharge T A hm hh sym rows zero conn b y)≤
      tariff*(A.positions+A.widthSum+((M).next b).positions+((M).next b).widthSum))
    (limit : (allocate K c op).next.heap≤heapEnd)
    (frame : SavedFrame cur ctr headerEnd (allocate K c op).next.header (allocate K c op).next.heap out final)
    (bounds : RefreshBounds headerEnd c.heap (allocate K c op).next.heap c.dense cur.val ctr.val) :
    let R:=Program.recastMove degreeEq M
    let b:=Program.degreeTerm degreeEq M branch
    let funding : Program.siteCharge M tariff:=⟨refreshBinaryCharge T A hm hh sym rows zero conn,fund⟩
    let f:=(Program.siteRecast degreeEq M funding).1 b
    ∀ (s₀ : R.ArchiveStep b old f),s₀=Program.recastArchiveStep degreeEq M funding branch old
      (refreshArchiveStep T A hm hh sym rows zero conn actual fit (fun i=>by simpa using published i 0)
        old numbered first) → ∀ L : A.Words Pins,allow (.refresh s h pad g C T) →
      RefreshWordVisit K cur ctr headerEnd heapEnd final allow R b L
        (Move.outputAssembler degreeEq M (refreshBinary_assembler T A hm hh sym rows zero conn) L b)
        old f s₀ := by
  let q : RefreshReceipt F K cur := ⟨s,rem,h,pad,D,tariff,g,C,γ,T,A,hm,hh,sym,rows,zero,conn,
    degreeEq,c,mid,out,branch,fit,old,numbered,first,stored,actual,published,histogram,fund⟩
  intro R b funding f s₀ eq L permitted
  subst s₀
  exact .native q limit frame bounds oldArrays L permitted

end Constructor
end
end RefreshJournal


def Parameters.archive (p : Parameters) (degree W : ℕ) : Archive where
  control := TickWorkspace.base p.age 40
  phase := TickWorkspace.base p.age 0+2
  rawStatic := p.rawTables+W*p.codebookWords
  rawCodebook := p.rawTables
  staticCodebook := TickWorkspace.base p.age 38
  codebookWords := p.codebookWords
  oldHistory := p.oldAux+1
  newHistory := p.newAux+1
  pairCapacity := p.historyCapacity
  seed := TickWorkspace.base p.age 20
  initialRecords := TickWorkspace.base p.age 49
  initialDegree := degree
  axes := p.axes
  relayWidth := p.wireWidth
  remainingLanes := 2^p.axes
  cursor := ⟨TickWorkspace.base p.age 20+64,TickWorkspace.base p.age 21,TickWorkspace.base p.age 22,
    0,TickWorkspace.base p.age 21+TickWorkspace.stride p.age/4,
    TickWorkspace.base p.age 21+TickWorkspace.stride p.age/2⟩
  K := p.symbolCap

def Parameters.banks (p : Parameters) : Banks :=
  ⟨TickWorkspace.base p.age 40,TickWorkspace.base p.age 43,TickWorkspace.base p.age 44,2^p.axes,
    p.perLanePairs,p.totalPairs,p.traceWork,p.unitWork⟩

def lastLayer (K : ℕ) : List Stage → Cursor → Layer → Layer
  | [],_,a => a
  | s::ss,c,_ => lastLayer K ss (allocate K c s).next (nodeLayer K c s)

def Parameters.nodeArchive (p : Parameters) (A : Archive) (ss : List Stage) (W : ℕ) : NodeArchive :=
  ⟨p.banks,TickWorkspace.base p.age 41,A.rawStatic+W*(64*(ss.length+2)),A.phase,A.control+3,
    maxRows childArity 0 ss,maxRows stageHalves (2*A.initialDegree) ss,maxRows stageMotifs 0 ss⟩

def Parameters.rootArchive (p : Parameters) (A : Archive) (a : NodeArchive) (ss : List Stage) (W : ℕ) :
    RootArchive :=
  let nr := ss.length+1
  let endLayer := lastLayer A.K ss A.cursor A.seedLayer
  let raw := a.rawHeader+W*(16*nr)
  ⟨p.age,A.control,TickWorkspace.base p.age 42,raw,raw+22*W,A.phase,A.cursor.heap,
    TickWorkspace.base p.age 46,TickWorkspace.base p.age 47,TickWorkspace.base p.age 48,
    TickWorkspace.base p.age 45,endLayer.first,endLayer.count,2^p.axes,p.perLanePairs,p.totalPairs,
    p.groups,p.chunkBits,p.slotBudget,nr,p.banks⟩

/-- All stage, child and owner pointers are computed from the single block's static
dimensions. None of the per-node graph or width data are accepted as parameters. -/
noncomputable def Parameters.machine {F : Type} [Field F] (p : Parameters) (B : Block F)
    (blocks residualBits : ℕ) : Procedure W :=
  let A := p.archive (2^(B.exponent 0)) W
  let ss := (B.repeat blocks).directory residualBits A.axes
  let N := p.nodeArchive A ss W
  let R := p.rootArchive A N ss W
  navigation A N R B blocks residualBits (R.rootCount*A.initialDegree)

noncomputable def Parameters.staticWords {F : Type} [Field F] (p : Parameters) (B : Block F)
    (blocks residualBits W : ℕ) : List ℕ :=
  let A := p.archive (2^(B.exponent 0)) W
  let ss := (B.repeat blocks).directory residualBits A.axes
  let N := p.nodeArchive A ss W
  let R := p.rootArchive A N ss W
  let layers := nodeLayers A.K ss A.cursor A.seedLayer
  A.directory ss (R.rootCount*A.initialDegree) W ++ nodeTape N.banks N.headerBase layers ++
    List.ofFn (fun j : Fin 22=>R.word j) ++ stageTape layers

theorem Parameters.staticWords_length {F : Type} [Field F] (p : Parameters) (B : Block F)
    (blocks residualBits W : ℕ) :
    (p.staticWords B blocks residualBits W).length=84*((B.repeat blocks).length+1)+86 := by
  simp [staticWords,Archive.directory_length,nodeTape_length,stageTape_length,nodeLayers_length,
    PhysicalStage.Program.directory_length]
  omega

/-- The metadata and role library share a single physical public parameter subsegment.
Its big-endian word mounting is the one used by the verified native tick input relation. -/
noncomputable def Parameters.mount {F : Type} [Field F] {q : ℕ} (p : Parameters) (B : Block F)
    (blocks residualBits W offset : ℕ) (library : List ℕ) (initial : Fin q→Bool) : Fin q→Bool :=
  let words := library ++ p.staticWords B blocks residualBits W
  RAM.TickParameterWords.mount (w:=W) offset words.length (fun i=>(words[i]?.getD 0 : ℕ)) initial

/-- Real fixed-grid cells and compactor tables occupy the beginning of the same physical
parameter suffix as every chronological header and node-publication record. -/
noncomputable def Parameters.gridWords {F : Type} [Field F] [Fintype F]
    (B : Block F) (u : ℕ) : List ℕ :=
  List.ofFn (fun i=>(RAM.HistoryStageBody.Physical.data B (16*u^10) (16*u^10) i).val)

@[simp] theorem Parameters.gridWords_length {F : Type} [Field F] [Fintype F] (B : Block F) (u : ℕ) :
    (Parameters.gridWords B u).length=RAM.HistoryStageBody.Physical.libraryWords B (16*u^10) := by
  simp [Parameters.gridWords]

noncomputable def Parameters.cursorMount {F : Type} [Field F] [Fintype F] {q : ℕ} (B : Block F)
    (u rem low stride cells : ℕ) (shape : RAM.PhysicalPinsExpr.Shape) (offset unitWork : ℕ)
    (initial : Fin q→Bool) : Fin q→Bool :=
  (Parameters.cursor B u rem low stride cells shape offset unitWork).mount
    B (u^8) rem (16*u^10) offset (Parameters.gridWords B u) initial


end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt
open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression PhysicalStage NavigationDirectory CompressorPacking Native
open RefreshDemandRows RefreshStageNav RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W K : ℕ} {cur ctr : Word W} {headerEnd:ℕ} {final:Memory W}
  (q : RefreshReceipt F K cur)
set_option quotPrecheck false
local notation "P" => CursorSpace.recordPointers q.entry
local notation "v" => Fintype.card q.input.Base
local notation "m" => 2^q.s
local notation "d" => 1+q.h+q.pad
local notation "N" => v*m*2^q.rem
local notation "Q" => refreshBinaryFamily q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn
local notation "pre" => (((refreshPre q.tile cur).pipeline cur).run q.mid)

theorem record_interval (t:Records.Table)
    (i:Fin (N*t.cols d)) : q.cursor.heap≤(P).dst t+i.val ∧ (P).dst t+i.val<q.entry.next.heap := by
  have prior:=CursorSpace.retained_addresses (c:=q.cursor) (K:=K) («v»:=v) (a:=q.s)
    (t:=q.rem) (h:=q.h) (pad:=q.pad)
  have start : q.cursor.heap+3*(v*2^q.rem)≤(P).kernel:=prior.2.1
  obtain ⟨_,a,b,c,last⟩:=CursorSpace.record_layout (c:=q.cursor) (K:=K) («v»:=v) (a:=q.s)
    (t:=q.rem) (h:=q.h) (pad:=q.pad)
  change (P).kernel+N*5=(P).motif at a
  change (P).motif+N*6=(P).headers at b
  change (P).headers+N*2=(P).halves at c
  change (P).halves+N*(8*d)≤q.entry.next.heap at last
  cases t <;> have hi:=i.isLt <;> simp only [Records.Table.cols,Records.Pointers.dst] at hi ⊢ <;> omega

/-- Every issued refresh table survives to the terminal archive. The two
control words are accounted for by their separation from this heap interval. -/
abbrev saved_records
    (saved : SavedFrame cur ctr headerEnd q.entry.next.header q.entry.next.heap q.out final)
    (header : headerEnd≤q.cursor.heap)
    (control : cur.val<q.cursor.heap ∨ q.entry.next.heap≤cur.val)
    (counter : ctr.val<q.cursor.heap ∨ q.entry.next.heap≤ctr.val) (t:Records.Table) :=
  let rows:=q.issued.records t
  fun site=>
    have span:=q.record_interval t (Records.rowOrder d t site)
    (saved _ (by omega) (by omega) (.inr (by omega)) span.2).trans (rows site)

/-- The branch's three admitted descriptor words are present both in the true
preparation image queried by the motif row, and in the final retained archive. -/
abbrev saved_choice
    (saved : SavedFrame cur ctr headerEnd q.entry.next.header q.entry.next.heap q.out final)
    (header : headerEnd≤q.cursor.heap)
    (control : cur.val<q.cursor.heap ∨ q.entry.next.heap≤cur.val)
    (counter : ctr.val<q.cursor.heap ∨ q.entry.next.heap≤ctr.val)
    (i:Fin (Q).motifs) (j:Fin 3) :=
  let a:=q.cursor.heap+(i.val*3+j.val)
  have lo : q.cursor.heap≤a:=by dsimp [a];omega
  have hi : a<q.cursor.heap+3*(v*2^q.rem):=by
    have x : i.val<v*2^q.rem:=i.isLt
    have y:=j.isLt
    dsimp [a];omega
  have start := (CursorSpace.retained_addresses (c:=q.cursor) (K:=K) («v»:=v) (a:=q.s)
    (t:=q.rem) (h:=q.h) (pad:=q.pad)).2.1
  have stop:=CursorSpace.record_layout (c:=q.cursor) (K:=K) («v»:=v) (a:=q.s)
    (t:=q.rem) (h:=q.h) (pad:=q.pad)
  have span : a<q.entry.next.heap:=by
    obtain ⟨_,e₁,e₂,e₃,e₄⟩:=stop
    change q.cursor.heap+3*(v*2^q.rem)≤(P).kernel at start
    change (P).kernel+N*5=(P).motif at e₁
    change (P).motif+N*6=(P).headers at e₂
    change (P).headers+N*2=(P).halves at e₃
    change (P).halves+N*(8*d)≤q.entry.next.heap at e₄
    omega
  have first:=q.issued.descriptors a lo hi
  have last:=saved a (by omega) (by omega) (.inr (by omega)) span
  And.intro (first.symm.trans (q.published i j)) (last.trans (q.published i j))

/-- Read each admitted packed quota in the retained terminal RAM window. -/
theorem saved_histogram
    (saved : SavedFrame cur ctr headerEnd q.entry.next.header q.entry.next.heap q.out final)
    (bounds : RefreshBounds headerEnd q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (i:Fin (Q).motifs) (j:Fin K) :
    final ((P).counts+K*i.val+j.val)=HistogramRegister.words ((Q).rows q.fit) ((Q).sequence q.fit q.branch) i j := by
  change final (q.cursor.dense+K*i.val+j.val)=_
  have hi:=q.histogram.1
  have mul:=Nat.mul_le_mul_left K i.isLt
  rw [Nat.mul_succ] at mul
  have hj:=j.isLt
  have bump : q.cursor.heap≤q.entry.next.heap:=by unfold entry;rw [heap_step];omega
  obtain ⟨_,⟨hc,ht⟩,hd⟩:=bounds
  exact (saved _ (by omega) (by omega) (.inr (by omega)) (by omega)).trans (q.histogram.2 i j)

set_option maxHeartbeats 1200000 in
/-- The checker reads the actual histogram indexed by the selected refresh tree. -/
theorem saved_quota
    (saved : SavedFrame cur ctr headerEnd q.entry.next.header q.entry.next.heap q.out final)
    (bounds : RefreshBounds headerEnd q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (i:Fin (Q).motifs) (a:Fin (Fintype.card ((Q).alphabet i))) :
    (final ((P).counts+K*i.val+a.val)).val=
      (((refreshBinaryBranchOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch)
        ((refreshBlockOrder q.input).symm i)).val ((Fintype.equivFin ((Q).alphabet i)).symm a)).val := by
  let letter:(Q).alphabet i:=(Fintype.equivFin _).symm a
  have value:=(Q).words_val q.fit q.branch i letter
  change _=(((Q).order q.branch i).val letter).val at value
  simp only [letter,Equiv.apply_symm_apply] at value
  exact (congrArg Fin.val (q.saved_histogram saved bounds i (a.castLE (q.fit.1 i)))).trans
    (value.trans (refreshBinaryFamily_symbol q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch i a))


end

end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

end OAI
