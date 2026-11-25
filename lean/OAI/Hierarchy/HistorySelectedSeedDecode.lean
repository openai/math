import OAI.Hierarchy.HistorySelectedPublisher
import OAI.Hierarchy.TraceReceiverVirtualLeaf

namespace OAI
/-! # The authentic virtual verifier and relay drive the selected command stream -/

namespace Hierarchy.HistorySelectedSeedDecode
open ThreeFlat Diagonal Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner RAM RAM.TraceBucketAtom
open RAM.BitLayout
open scoped Classical Fin.CommRing

variable {F : Type} [Fintype F] [Field F] {w W p S f q low b : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (L : Lane (q+1))
    (copies raw dict masks gateBase : ℕ) (field : Fintype.card F ≤ 2^W)
set_option quotPrecheck false

local notation "traceDepth" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k traceDepth
local notation "keys" => TraceBitDescriptor.records (p:=p) (r:=r) (k:=k) (d:=traceDepth) hw base S f
local notation "ports" => Fintype.card (TraceAddressRecord.StaticPortIndex w p r k traceDepth)
local notation "N" => network hF hw hp base st hs hf r k traceDepth
local notation "ids" => gateBase + FixedTraceImage.count G
local notation "params" => ids + (G).cells
local notation "V" => (⟨raw,(N).cells,params⟩ : TraceRawLookup.Layout)
local notation "B" => bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies raw dict masks ids
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "I" => bitIndex hF hw hp base st hs hf r k fit L
local notation "A" => bitAddress hF hw hp base st hs hf r k fit L I
local notation "L0" => (I).firstNetwork (r:=copies) A 0
local notation "ln" => (finFunctionFinEquiv L).val
local notation "enc" => FieldCode.ofCardLe field
local notation "args" => FixedTraceProgram.publicWords G enc S
  (TraceUniformRow.SharedCount w p r k traceDepth f) raw gateBase (gateBase+11*(G).cells)


open RAM.HistoryInitialSeed TraceReceiverVirtualLeaf
/-- Direct source banks after construction on this receiver. -/
structure Installed (m : Memory W) : Prop where
  mounted : Mounted (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k raw gateBase field m
  dictionary : ∀ a : Occurrence N, (m (dict+((P).offset ((P).code a)).val)).val=((P).code a).val
  offsets : ∀ i, (m (masks+i.val)).val=((P).offset i).val

/-- Scalar address/size bounds shared by all visits to the same sparse prototype. -/
structure Fits : Prop where
  portEnd : gateBase+11*(G).cells+11*ports≤2^W
  safe : ∀ (v : Fin (2^traceDepth)) i, (keys i).Fits W v.val
  sources : 2+ports+(G).internal<2^W
  cells : (G).cells<2^W
  eleven : 11<2^W
  head : params+FixedTraceProgram.P≤2^W
  endRaw : raw+11*(N).cells<2^W
  beforeIds : raw+11*(N).cells ≤ ids
  beforeDict : raw+11*(N).cells≤dict
  beforeMasks : raw+11*(N).cells≤ masks
  size : (B).footprint<2^b
  word : 5*b+128≤W
  recordEnd : (B).records+11*((B).shape.rows*(B).slots)+4≤2^W
  dictEnd : (B).dictionary+(B).shape.rows≤2^W
  maskEnd : (B).masks+(1+2*traceDepth)≤2^W
  idEnd : (B).tableIds+(B).slots≤2^W
  coeff : Fintype.card F≤2+S+(B).shape.count
  labels : Fintype.card ((Fin 3→Bool)→F)≤2^W

local notation "ready" m:arg => Installed (q:=q) (low:=low) (S:=S) (f:=f)
  hF hw hp base st hs hf r k fit raw dict masks gateBase field m
local notation "room" => Fits (q:=q) (low:=low) (S:=S) (f:=f) (b:=b) (W:=W)
  hF hw hp base st hs hf r k copies raw dict masks gateBase

theorem Installed.retain (Y : HistoryInitialSeed.Layout) (z : Site) {src m : Memory W}
    (old : ready src) (keep : z.retains Y m src)
    (template : Protected Y z gateBase (TraceReceiverTemplate.count G))
    (dictionary : Protected Y z dict (2^traceDepth)) (mask : Protected Y z masks (1+(traceDepth+traceDepth))) :
    ready m := by
  refine ⟨fun i hi=>(template.read keep i hi).trans (old.mounted i hi),?_,?_⟩
  · intro a
    rw [dictionary.read keep _ (by simpa only [pow_add] using ((P).offset ((P).code a)).isLt)]
    exact old.dictionary a
  · intro i
    rw [mask.read keep _ i.isLt]
    exact old.offsets i

theorem first_reads (Y : HistoryInitialSeed.Layout) (z : Site) (rest : Fin 1→Word W)
    (src : Memory W) (image : ready src) (size : room)
    (template : Protected Y z gateBase (TraceReceiverTemplate.count G))
    (dictionary : Protected Y z dict (2^traceDepth)) (mask : Protected Y z masks (1+(traceDepth+traceDepth)))
    (lane : z.lane=ln) (laneFit : z.lane<2^W)
    (zero : z.stage=0) (count : (L0).cells=z.rows Y) :
    HistorySelectedSeed.RawReads Y z (TraceRawLookup.virtual W V (publicProgram W))
      (publicData B rest) src (recordAt tableId L0 (z.stream Y)) := by
  apply HistorySelectedSeed.metadata_reads Y z _ _ _ _ _ count (by have:=size.eleven; omega)
  intro m keep i j vs row col lnAt stageAt
  have stored : ready m := Installed.retain hF hw hp base st hs hf r k fit raw dict masks gateBase field
    Y z image keep template dictionary mask
  have sourceRows := source hF hw hp base st hs hf r k raw gateBase field m stored.mounted
    size.portEnd size.safe size.sources size.cells size.eleven
  apply first hF hw hp base st hs hf r k fit L copies raw dict masks gateBase field m sourceRows
    size.head size.endRaw size.beforeIds size.beforeDict size.beforeMasks size.size size.word
    size.recordEnd size.dictEnd size.maskEnd size.idEnd size.coeff
    (label hF hw hp base st r k raw gateBase field m stored.mounted size.labels)
    stored.dictionary stored.offsets rest vs i j row col
  · rw [lnAt,Fin.val_cast_of_lt laneFit,lane]
  · simp [stageAt,zero]

theorem later_reads (Y : HistoryInitialSeed.Layout) (z : Site) (rest : Fin 1→Word W)
    (src : Memory W) (image : ready src) (size : room)
    (template : Protected Y z gateBase (TraceReceiverTemplate.count G))
    (dictionary : Protected Y z dict (2^traceDepth)) (mask : Protected Y z masks (1+(traceDepth+traceDepth)))
    (lane : z.lane=ln) (laneFit : z.lane<2^W)
    (stage : Fin (q+1)) (time : z.stage=stage.val) (positive : stage.val≠0) (stageFit : z.stage<2^W)
    (count : (RelayNetwork.network (F:=F) (r:=copies) (I).tag (P).mask stage).cells=z.rows Y) :
    HistorySelectedSeed.RawReads Y z (TraceRawLookup.virtual W V (publicProgram W))
      (publicData B rest) src (recordAt (tableId (F:=F)) (RelayNetwork.network (F:=F) (r:=copies) (I).tag (P).mask stage)
        (z.stream Y)) := by
  apply HistorySelectedSeed.metadata_reads Y z _ _ _ _ _ count (by have:=size.eleven; omega)
  intro m keep i j vs row col lnAt stageAt
  have stored : ready m := Installed.retain hF hw hp base st hs hf r k fit raw dict masks gateBase field
    Y z image keep template dictionary mask
  have sourceRows := source hF hw hp base st hs hf r k raw gateBase field m stored.mounted
    size.portEnd size.safe size.sources size.cells size.eleven
  have budget := capacity hF hw hp base st hs hf r k fit copies raw dict masks gateBase field m
    size.beforeMasks size.size size.word size.recordEnd size.dictEnd size.maskEnd size.idEnd size.coeff stored.offsets
  apply later hF hw hp base st hs hf r k fit L copies raw dict masks gateBase field m sourceRows
    size.head size.endRaw budget rest vs stage positive i j row col
  · rw [lnAt,Fin.val_cast_of_lt laneFit,lane]
  · rw [stageAt,Fin.val_cast_of_lt stageFit,time]

end Hierarchy.HistorySelectedSeedDecode

end OAI
