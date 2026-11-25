import OAI.Hierarchy.TraceRefreshRetained
import OAI.ThreeFlat.Diagonal.NavigationArchive
import OAI.ThreeFlat.Diagonal.NavigationQuotaImage

namespace OAI
/-! # A refresh transition on the mounted chronological archive

The native call consumes exactly the shared bit interval selected by the cumulative
motif counts. It advances the live archive and returns the graph, stage descriptors
and selected histogram for the same branch at the machine's actual word width.
-/

noncomputable section
namespace Hierarchy.TraceRefreshArchivePass

open ThreeFlat Diagonal Diagonal.NavigationPass Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure NavigationDirectory
open Computability.VPVNP.Compression CompressorPacking Native RefreshDemandRows RefreshTies RefreshStageNav
open scoped Classical BigOperators Fin.CommRing
variable {F : Type} [Field F] {W q s rem h pad : ℕ} {g : Fin (2^s)→Fin (2^s)→ℕ} {C γ : ℝ}
    (a : Archive) (T : RefreshMotif.Table F g (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,g i j=g j i) (rows : ∀ i,∑ j,g i j=h)
    (zero : ∀ i,g i i=0) (conn : Expander.Bound (Expander.transition g h) ℝ γ)
set_option quotPrecheck false
local notation "d" => 2^s
local notation "v" => Fintype.card A.Base
local notation "step" => Stage.refresh v d (2^rem) h pad
local notation "M" => refreshBinary T A hm hh sym rows zero conn
local notation "Q" => refreshBinaryFamily T A hm hh sym rows zero conn

theorem onArchive (field : FieldCode F W) (room : TraceRetainedRoom.Room q W) (width : 0<W) (cur : Word W) (m₀ : Memory W)
    (pre post : List Stage) (edges cap : ℕ) (raw : ℕ→Bool) (fit : (Q).Fits a.K W)
    (alphabet : refreshSymbolBound T≤a.K) (fixed : refreshFixedWords T≤q) (count : a.K≤q)
    (arena : (step).heapWords≤q) (wire : A.maxWidth+1≤q^4) :
    let steps:=pre++step::post
    let c:=finish a.K pre a.cursor
    let entry:=allocate a.K c step
    let rawBits:=(List.ofFn (fun i : Fin cap=>raw i.val)).drop (W*(a.K*(pre.map Stage.motifs).sum))
    a.Live steps edges raw cur c m₀ → a.cursor.header=a.seed+64 →
    a.seed+(a.directory steps edges W).length≤a.cursor.dense →
    a.cursor.dense+a.histWords steps≤c.heap → c.header+64≤a.cursor.dense →
    c.graph+6*(v*d)≤c.heap → c.width+v*d*(d*2^rem)≤c.heap →
    entry.next.heap≤cur.val → W*(a.K*(pre.map Stage.motifs).sum)+(Q).motifs*a.K*W≤cap →
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
              ((refreshBlockOrder A).symm i)).val else Fintype.card ((Q).alphabet i):ℕ):Word W)) ∧
          QuotaImage Q fit j c out ∧ c.header+64*(post.length+1)≤c.dense) ∧
        ∀ k,k≠cur.val → (k<c.heap ∨ entry.next.heap≤k) → out k=m₀ k)
      (refreshCallTime T A sym rows zero a.K cur c) := by
  intro steps c entry rawBits live origin table dense later graph widths ctrl capRoom old body middle
  have bump : c.heap≤entry.next.heap := by dsimp only [entry];rw [heap_step];omega
  have high : c.heap≤cur.val := bump.trans ctrl
  have static : a.seed+(a.directory steps edges W).length≤c.heap := table.trans (by omega)
  have tableFit : a.seed+(a.directory steps edges W).length<2^W := static.trans_lt (high.trans_lt cur.isLt)
  have locals := live.input Q (by rfl) fit cap capRoom
  let digit:=RawHistogram.stage (W:=W) (Q).motifs a.K raw (a.K*(pre.map Stage.motifs).sum)
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
  obtain ⟨vb,lb,db,sb,rom,rot,full,tiles,kf,wb,top⟩:=TraceRefreshRetained.scalarRoom T A room fixed count arena wire
  intro np nr nk machine pc reg pub exit inst data config mem atPc initial
  obtain ⟨accept,reject⟩:=refresh_admission T A hm hh sym rows zero conn field width cur m₀ c here old fit digit
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



end Hierarchy.TraceRefreshArchivePass

end
end OAI
