import OAI.Hierarchy.TraceShrinkRetained
import OAI.ThreeFlat.Diagonal.NavigationArchiveVisit
import OAI.ThreeFlat.Diagonal.ShrinkCursorColumns

namespace OAI
/-! # Chronological raw-bit and graph transition of the native shrink instruction -/

namespace Hierarchy.TraceShrinkRetained
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure NavigationDirectory
noncomputable section
open Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink
open scoped Classical
variable {F : Type} [Field F] {W q : ℕ} (a : Archive) (T : ShrinkMotif.Table F) (s D rem : ℕ)
    (hD : 0<D) (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024)
    (A : State (2^s) (shrinkCharge s+rem))
set_option quotPrecheck false
local notation "d" => (2^s:ℕ)
local notation "N" => Fintype.card (shrinkRecordState s rem A).Base
local notation "x" => dims (shrinkStage s D) N (CompressorPacking.tagBits d) rem
local notation "step" => Stage.shrink x
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A

/-- The actual native shrinking call on a chronological archive chooses the canonical next
history branch and leaves the exact resident graph for either type of following instruction. -/
theorem onArchive (field : FieldCode F W) (word : 0<W) (room : TraceRetainedRoom.Room q W) (cur : Word W) (m₀ : Memory W)
    (pre post : List Stage) (edges cap : ℕ) (raw : ℕ→Bool)
    (fit : (Q).Fits a.K W) (alphabet : shrinkSymbolBound T≤a.K)
    (fixed : fixedWords T s D≤q) (arena : (step).heapWords≤q)
    (wire : A.maxWidth+1≤q^4) :
    let steps:=pre++step::post
    let c:=finish a.K pre a.cursor
    let entry:=allocate a.K c step
    let rawBits:=(List.ofFn (fun i : Fin cap=>raw i.val)).drop (W*(a.K*(pre.map Stage.motifs).sum))
    a.Live steps edges raw cur c m₀ → a.cursor.header=a.seed+64 →
    a.seed+(a.directory steps edges W).length≤a.cursor.dense →
    a.cursor.dense+a.histWords steps≤c.heap → c.header+64≤a.cursor.dense →
    c.header+64≤c.graph → c.header+64≤c.width →
    c.graph+6*(x).oldEdges≤c.heap → c.width+(x).oldEdges*(x).originalLanes≤c.heap →
    entry.next.heap≤cur.val → W*(a.K*(pre.map Stage.motifs).sum)+(Q).motifs*a.K*W≤cap →
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
  have static : a.seed+(a.directory steps edges W).length≤c.heap := table.trans (by omega)
  have tableFit : a.seed+(a.directory steps edges W).length<2^W := static.trans_lt (high.trans_lt cur.isLt)
  have widthCount : (Q).motifs=(step).motifs := by
    rw [shrinkBinaryFamily_motifs]
    change Fintype.card A.Base*_ * _ * _ * _ * _=N*_ * _ * _ * _ * _
    rw [shrink_record_base s rem A]
    simp only [dims,shrinkStage]
  have locals := live.input Q widthCount fit cap capRoom
  let digit:=RawHistogram.stage (W:=W) (Q).motifs a.K raw (a.K*(pre.map Stage.motifs).sum)
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
  obtain ⟨accept,reject⟩:=admission_of_room T s D rem hD small A room word field cur m₀ c here
    (by rw [shrink_input_columns]; exact old) ⟨nextGraph,nextWidth⟩
    fit digit locals.1 fixed arena wire alphabet machine pc reg pub exit inst data config mem atPc initial
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


end
end Hierarchy.TraceShrinkRetained

end OAI
