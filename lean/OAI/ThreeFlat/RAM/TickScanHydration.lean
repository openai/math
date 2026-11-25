import OAI.ThreeFlat.RAM.TickExecutionInputs
import OAI.ThreeFlat.RAM.TickGroupScanInputs
import OAI.ThreeFlat.RAM.TickScanRanges

namespace OAI
/-! # The physical group scan directly from the navigator's staged output -/

noncomputable section

namespace ThreeFlat.RAM.TickActiveROM

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickChronology Diagonal.TickGroupIntervals
open BitLayout Contraction TickIntervalCursor TickBitRelation
open scoped Fin.CommRing

variable {F : Type*} [Field F] [Fintype F] {p H J w : ℕ}
    {B : Layout} {clock : Clock} {fit : Fits (TickWeightedBank.shape F p H J) w}

/-- Every read in this record refers to the navigator's own output, before
the pair-pointer setup and before generation of the auxiliary request words. -/
structure ScanWords (x : CellInput B clock fit) (out : Memory w) : Prop where
  disjoint : x.intervals.Pairwise Compatible
  chunkFits : x.lo+B.bits < 2^w
  groupFits : x.group < 2^w
  rowsFit : ∀ e ∈ x.intervals, FitsRow e w
  count : out B.intervalCount = (x.intervals.length : Word w)
  chunk : out (B.clockWords+2) = (x.lo : Word w)
  group : out B.clockWords = (x.group : Word w)
  rows : ∀ i : Fin x.intervals.length, ∀ j : Fin 4,
    out (B.intervalTable+4*i.val+j.val) = (intervalColumn x.intervals[i.val] j : Word w)
  mapZero : ∀ j < B.bits, out (B.intervalMap+j) = 0
  packedBound : ∀ i : Fin (TickChunkCheck.chunkSize (TickGroupScanBank.layout B.scan x.lo x.group)),
    TickChunkCheck.codeAt (TickGroupScanBank.layout B.scan x.lo x.group) x.intervals i.val ≤ x.count
  before : ∀ j < x.count, out (B.oldAux+x.aux.wiresEnd+j) = TickBitRelation.bitWord w (x.before j)
  after : ∀ j < x.count, out (B.oldAux+x.aux.wiresEnd+x.count+j) = TickBitRelation.bitWord w (x.after j)

open scoped Fin.CommRing Classical

theorem CellInput.scanInputs_of_words (x : CellInput B clock fit) (out : Memory w) (oc nc : Fin B.bits → Bool)
    (hb : WordBounds B fit) (r : ScanRanges B x.intervals.length w) (raw : ScanWords x out)
    (selected : TickPairHeader.selected out B.clockWords B.groupCounts clock.groups = (x.count : Word w))
    (oldChunk : ∀ i : Fin B.bits, out (B.oldChunk+i.val) = TickBitRelation.bitWord w (oc i))
    (newChunk : ∀ i : Fin B.bits, out (B.newChunk+i.val) = TickBitRelation.bitWord w (nc i)) :
    TickGroupScanBank.ScanInputs w B.scan x.intervals x.lo x.group (x.filled .scan out)
      x.before x.after (chunkView B x.lo x.group oc) (chunkView B x.lo x.group nc) := by
  have bclk := hb.clk
  have bb := hb.bounds
  have ba := hb.oldAux
  have bo := hb.oldChunk
  have bn := hb.newChunk
  have bfit := hb.requests
  have q₃ := r.auxChunk
  have q₄ := r.chunkTable
  have q₅ := r.tableCount
  have q₆ := r.countMap
  have q₇ := r.mapFit
  have fitBounds : B.bounds+4 ≤ 2^w := by omega
  have auxEnd : x.aux.wiresEnd+2*x.count ≤ B.bits := x.pairSpace
  have frame (k : ℕ) (away : k<B.auxRequest ∨ B.auxRequest+8*B.bits≤k) :
      x.filled .scan out k = boundsMemory B clock out k := by
    unfold CellInput.filled fillSegment
    exact ite_eq_right (by omega)
  have low (k : ℕ) (hk : k<B.bounds) : x.filled .scan out k = out k :=
    (frame k (Or.inl (by omega))).trans (bounds_low B clock out k hk fitBounds)
  have high (k : ℕ) (hk : B.intervalTable≤k) : x.filled .scan out k = out k :=
    (frame k (Or.inr (by omega))).trans (bounds_high B clock out k (by omega) fitBounds)
  have hcache := bound_values B clock out x.count x.pairSpace fitBounds selected
  have ptr₀ : x.filled .scan out (B.bounds+2) = ((B.oldAux+x.aux.wiresEnd : ℕ) : Word w) := by
    rw [frame _ (Or.inl (by omega))]
    exact hcache 2
  have ptr₁ : x.filled .scan out (B.bounds+3) = ((B.oldAux+x.aux.wiresEnd+x.count : ℕ) : Word w) := by
    rw [frame _ (Or.inl (by omega))]
    exact hcache 3
  have table : Stores (x.filled .scan out) B.intervalTable x.intervals := by
    let row := fun i : Fin x.intervals.length => x.intervals[i.val]
    have hm (i : Fin x.intervals.length) (j : Fin 4) :
        x.filled .scan out (B.intervalTable+4*i.val+j.val) = (intervalColumn (row i) j : Word w) :=
      (high (B.intervalTable+4*i.val+j.val) (by omega)).trans (raw.rows i j)
    simpa only [row,List.ofFn_getElem] using stores_of_columns _ B.intervalTable row hm
  let L := TickGroupScanBank.layout B.scan x.lo x.group
  have pin (base : ℕ) (bits : Fin B.bits → Bool) (ok : base+B.bits ≤ B.bounds)
      (read : ∀ i : Fin B.bits, out (base+i.val) = TickBitRelation.bitWord w (bits i)) (i : Fin (TickChunkCheck.chunkSize L)) :
      x.filled .scan out (base+i.val) = TickBitRelation.bitWord w (chunkView B x.lo x.group bits i) := by
    let j : Fin B.bits := i.cast (TickGroupScanBank.size B.scan x.lo x.group)
    change x.filled .scan out (base+j.val) = TickBitRelation.bitWord w (bits j)
    exact (low (base+j.val) (by have := j.isLt; omega)).trans (read j)
  apply TickGroupScanBank.ScanInputs.of_ranges B.scan x.intervals x.lo x.group _ x.before x.after _ _
    x.count (B.oldAux+x.aux.wiresEnd) (B.oldAux+x.aux.wiresEnd+x.count) raw.disjoint hb.width raw.chunkFits
    raw.groupFits q₄ (by change B.intervalTable+4*x.intervals.length ≤ B.intervalMap; omega) q₇
    (by change B.intervalCount<B.intervalMap ∧ B.clockWords+2<B.intervalMap ∧ B.clockWords<B.intervalMap; omega)
    ((high B.intervalCount (by omega)).trans raw.count) ((low (B.clockWords+2) (by omega)).trans raw.chunk)
    ((low B.clockWords (by omega)).trans raw.group) raw.rowsFit table
    (fun j hj => (high (B.intervalMap+j) (by omega)).trans (raw.mapZero j hj)) raw.packedBound
    (by change B.bounds+2<B.chunkRequest ∧ B.bounds+3<B.chunkRequest; omega)
    (by change B.oldAux+x.aux.wiresEnd+x.count≤B.chunkRequest ∧
          B.oldAux+x.aux.wiresEnd+x.count+x.count≤B.chunkRequest; omega) ptr₀ ptr₁
    (fun j hj => (low (B.oldAux+x.aux.wiresEnd+j) (by omega)).trans (raw.before j hj))
    (fun j hj => (low (B.oldAux+x.aux.wiresEnd+x.count+j) (by omega)).trans (raw.after j hj))
    (by change B.oldChunk+B.bits≤B.chunkRequest ∧ B.newChunk+B.bits≤B.chunkRequest; omega)
    (pin _ _ bo oldChunk) (pin _ _ bn newChunk)

/-- Assemble the full navigation contract with pure staged inputs at scan
ticks; the other phases need no interval table. -/
theorem NavOutput.of_staged (x : CellInput B clock fit) (ph : Phase) (out : Memory w)
    (oa na oc nc : Fin B.bits → Bool) (slotInput : Memory w → Prop) (hb : WordBounds B fit)
    (selected : TickPairHeader.selected out B.clockWords B.groupCounts clock.groups = (x.count : Word w))
    (phase : out (B.control+2) = (ph.tag : Word w)) (marker : out (B.control+3) = 1)
    (oldAux : ∀ i : Fin B.bits, out (B.oldAux+i.val) = TickBitRelation.bitWord w (oa i))
    (newAux : ∀ i : Fin B.bits, out (B.newAux+i.val) = TickBitRelation.bitWord w (na i))
    (oldChunk : ∀ i : Fin B.bits, out (B.oldChunk+i.val) = TickBitRelation.bitWord w (oc i))
    (newChunk : ∀ i : Fin B.bits, out (B.newChunk+i.val) = TickBitRelation.bitWord w (nc i))
    (scan : ph=.scan → ScanRanges B x.intervals.length w ∧ ScanWords x out)
    (eval : ph=.evaluate → slotInput (x.filled ph out)) :
    NavOutput x ph oa na oc nc slotInput out := by
  refine ⟨selected,phase,marker,oldAux,newAux,oldChunk,newChunk,?_,eval⟩
  rintro rfl
  exact x.scanInputs_of_words out oc nc hb (scan rfl).1 (scan rfl).2 selected oldChunk newChunk



end ThreeFlat.RAM.TickActiveROM

end
end OAI
