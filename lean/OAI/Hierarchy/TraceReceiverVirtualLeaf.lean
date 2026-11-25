import OAI.Hierarchy.TraceReceiverTemplateMount
import OAI.ThreeFlat.Diagonal.TraceVirtualSource
import OAI.ThreeFlat.Diagonal.TraceBucketReady
import OAI.ThreeFlat.Diagonal.TraceBucketRomFits
import OAI.ThreeFlat.RAM.TraceRawLookup

namespace OAI
/-! # Native metadata readback at the physical cursor leaves -/

namespace Hierarchy.TraceReceiverVirtualLeaf

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

local notation "depth" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k depth
local notation "keys" => TraceBitDescriptor.records (p:=p) (r:=r) (k:=k) (d:=depth) hw base S f
local notation "ports" => Fintype.card (TraceAddressRecord.StaticPortIndex w p r k depth)
local notation "N" => network hF hw hp base st hs hf r k depth
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
  (TraceUniformRow.SharedCount w p r k depth f) raw gateBase (gateBase+11*(G).cells)

/-- The row generator has an absolute instruction bound independent of every
width, selected address, local M table and total verifier row count. -/
theorem row_binds (R : TraceRawLookup.Layout) (W : ℕ) :
    (TraceRawLookup.virtual W R (publicProgram W)).binds ≤ 866000000 := by
  exact (TraceRawLookup.virtual_binds W R _).trans
    (Nat.mul_le_mul_left 866 (publicProgram_size W))

/-- Physical template reads hold after mounting the genuine structural header
and persist across any subsequent writes outside that compact segment. -/
def Mounted (m : Memory W) := ∀ i, i < TraceReceiverTemplate.count G →
  m (gateBase+i) = TraceReceiverTemplate.scalar G enc keys args i

/-- All scalar accesses to the expanded verifier are served through the fixed
row expression, for any camera lane and any selected address. -/
theorem source (m : Memory W) (mounted : Mounted (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k raw gateBase field m)
    (portEnd : gateBase+11*(G).cells+11*ports ≤ 2^W)
    (safe : ∀ (v : Fin (2^depth)) i, (keys i).Fits W v.val)
    (sources : 2+ports+(G).internal < 2^W) (cells : (G).cells < 2^W) (eleven : 11 < 2^W) :
    TraceRawLookup.Sources N enc V m := by
  apply TraceBitPhysical.physical_source (r:=r) (k:=k) (d:=depth) hF hw hp hs hf base st enc raw gateBase params m
  · intro i
    let j := FixedTraceImage.count G+(G).cells+(FixedTraceProgram.extra i).val
    have h : j < TraceReceiverTemplate.count G := by
      dsimp [j,TraceReceiverTemplate.count]; have := (FixedTraceProgram.extra i).isLt; omega
    simpa [j,Nat.add_assoc] using (mounted j h).trans (TraceReceiverTemplate.arg G enc keys args i)
  · intro i j
    have h : 11*i.val+j.val < TraceReceiverTemplate.count G := by
      unfold TraceReceiverTemplate.count FixedTraceImage.count; have := i.isLt; have := j.isLt; omega
    simpa [Nat.add_assoc] using (mounted _ h).trans (TraceReceiverTemplate.gate G enc keys args i j)
  · intro i j
    have h : 11*(G).cells+(11*i.val+j.val) < TraceReceiverTemplate.count G := by
      have hi : i.val < Fintype.card (TraceStaticRow.Port w p r k depth) := i.isLt
      unfold TraceReceiverTemplate.count FixedTraceImage.count
      have hj := j.isLt
      omega
    simpa [TraceAddressReader.address,Nat.add_assoc] using
      (mounted _ h).trans (TraceReceiverTemplate.port G enc keys args i j)
  · omega
  · exact portEnd
  · exact safe
  · exact sources
  · exact cells
  · exact eleven

/-- The canonical table ID also comes from the same physical input. -/
theorem label (m : Memory W) (mounted : Mounted (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k raw gateBase field m)
    (fits : Fintype.card ((Fin 3 → Bool) → F) ≤ 2^W) (i : Fin (G).cells) :
    (m (ids+i.val)).val = ((HistoryCompiledRows.library G).id i).val := by
  have hi : FixedTraceImage.count G+i.val < TraceReceiverTemplate.count G := by
    unfold TraceReceiverTemplate.count; have := i.isLt; omega
  have read := (mounted _ hi).trans (TraceReceiverTemplate.label G enc keys args i)
  rw [Nat.add_assoc,read]
  exact Fin.val_cast_of_lt (((HistoryCompiledRows.library G).id i).isLt.trans_le fits)

/-- The numerical image-capacity certificate uses the genuine verifier record
expression, with no hypothesis about the contents of a global record bank. -/
theorem capacity (m : Memory W) (beforeMasks : raw+11*(N).cells ≤ masks)
    (size : (B).footprint < 2^b) (word : 5*b+128 ≤ W)
    (recordEnd : (B).records+11*((B).shape.rows*(B).slots)+4 ≤ 2^W)
    (dictEnd : (B).dictionary+(B).shape.rows ≤ 2^W)
    (maskEnd : (B).masks+(1+2*depth) ≤ 2^W) (idEnd : (B).tableIds+(B).slots ≤ 2^W)
    (coeff : Fintype.card F ≤ 2+S+(B).shape.count)
    (offsets : ∀ i, (m (masks+i.val)).val=((P).offset i).val) :
    ImageCapacity B (TraceRawOverlay.memory N enc raw m) b := by
  let o := TraceRawOverlay.memory N enc raw m
  have loaded := TraceRawOverlay.loaded N enc raw m
  apply capacity_of_records hF hw hp base st hs hf r k fit copies raw dict masks ids field o
    size word recordEnd dictEnd maskEnd idEnd coeff
    (ready_four hF hw hp base st hs hf r k fit copies raw dict masks ids enc o loaded)
  intro z
  have beyond : raw+11*(N).cells ≤ masks+z.val := by omega
  exact (congrArg Fin.val (TraceRawOverlay.outside N enc raw m (.inr beyond))).trans (offsets z)

/-- The leaf reads it makes from the large virtual gate image are the genuine
verifier rows. Only the small physical mask, dictionary and label banks are
accessed directly. -/
theorem first (m : Memory W) (src : TraceRawLookup.Sources N enc V m)
    (headFit : params+FixedTraceProgram.P ≤ 2^W) (endFit : raw+11*(N).cells < 2^W)
    (beforeIds : raw+11*(N).cells ≤ ids) (beforeDict : raw+11*(N).cells ≤ dict)
    (beforeMasks : raw+11*(N).cells ≤ masks)
    (size : (B).footprint < 2^b) (word : 5*b+128 ≤ W)
    (recordEnd : (B).records+11*((B).shape.rows*(B).slots)+4 ≤ 2^W)
    (dictEnd : (B).dictionary+(B).shape.rows ≤ 2^W)
    (maskEnd : (B).masks+(1+2*depth) ≤ 2^W) (idEnd : (B).tableIds+(B).slots ≤ 2^W)
    (coeff : Fintype.card F ≤ 2+S+(B).shape.count)
    (labels : ∀ i : Fin (G).cells, (m (ids+i.val)).val = ((HistoryCompiledRows.library G).id i).val)
    (dictionary : ∀ a : Occurrence N, (m (dict+((P).offset ((P).code a)).val)).val=((P).code a).val)
    (offsets : ∀ i, (m (masks+i.val)).val=((P).offset i).val)
    (rest : Fin 1→Word W) (v : Fin 4→Word W) (i : Fin (L0).cells) (j : Fin 4)
    (row : (v 0).val=i.val) (col : (v 1).val=j.val) (lane : (v 2).val=ln) (stage : (v 3).val=0) :
    (TraceRawLookup.virtual W V (publicProgram W)).eval (publicData B rest) m v =
      (HistoryCompiledRows.metadata tableId L0 i j : Word W) := by
  let o := TraceRawOverlay.memory N enc raw m
  have loaded := TraceRawOverlay.loaded N enc raw m
  have maskRead (z : Fin (1+(depth+depth))) : (o (masks+z.val)).val=((P).offset z).val := by
    rw [show o (masks+z.val) = m (masks+z.val) from
      TraceRawOverlay.outside N enc raw m (.inr (by omega))]
    exact offsets z
  have budget : ImageCapacity B o b := capacity hF hw hp base st hs hf r k fit copies raw dict masks
    gateBase field m beforeMasks size word recordEnd dictEnd maskEnd idEnd coeff offsets
  rw [TraceRawLookup.eval_virtual N enc V m _ _ _ rfl endFit headFit src]
  apply ready_first hF hw hp base st hs hf r k fit L copies raw dict masks ids enc o budget loaded
    _ _ maskRead rest v i j row col lane stage
  · intro z
    exact (congrArg Fin.val (TraceRawOverlay.outside N enc raw m (a:=ids+z.val)
      (.inr (beforeIds.trans (Nat.le_add_right _ _))))).trans (labels z)
  · intro a
    exact (congrArg Fin.val (TraceRawOverlay.outside N enc raw m (a:=dict+((P).offset ((P).code a)).val)
      (.inr (beforeDict.trans (Nat.le_add_right _ _))))).trans (dictionary a)

/-- Positive-cursor gates use the actual physical relay network of the same
lane and share the same evaluation and workspace bound as the first cursor. -/
theorem later (m : Memory W) (src : TraceRawLookup.Sources N enc V m)
    (headFit : params+FixedTraceProgram.P ≤ 2^W) (endFit : raw+11*(N).cells < 2^W)
    (budget : ImageCapacity B (TraceRawOverlay.memory N enc raw m) b)
    (rest : Fin 1→Word W) (v : Fin 4→Word W) (stage : Fin (q+1)) (positive : stage.val ≠ 0)
    (i : Fin (B).relays) (j : Fin 4) (row : (v 0).val=i.val) (col : (v 1).val=j.val)
    (lane : (v 2).val=ln) (atStage : (v 3).val=stage.val) :
    (TraceRawLookup.virtual W V (publicProgram W)).eval (publicData B rest) m v =
      (HistoryCompiledRows.metadata (tableId (F:=F)) (RelayNetwork.network (r:=copies) (I).tag (P).mask stage) i j : Word W) := by
  rw [TraceRawLookup.eval_virtual N enc V m _ _ _ rfl endFit headFit src]
  exact ready_later hF hw hp base st hs hf r k fit L copies raw dict masks ids _ budget rest v
    stage positive i j row col lane atStage


end Hierarchy.TraceReceiverVirtualLeaf

end OAI
