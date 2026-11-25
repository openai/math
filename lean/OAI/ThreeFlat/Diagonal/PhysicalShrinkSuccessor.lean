import OAI.ThreeFlat.Diagonal.PhysicalShrinkImage

namespace OAI
/-! # Native successor images for the actual branch of the chronological move -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.Compression CompressorPacking Native PhysicalShrink
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

/-- A branch memory is addressed by the native term ordinal. -/
def Move.Images {d lanes D rem : ℕ} {A : State d lanes} (R : Move F A D rem)
    (C : SlotImage.Columns) (mem : ℕ → ℕ → ℕ) : Prop :=
  ∀ j, SlotImage.Stored (R.next j).graph (R.next j).order (tagOrdinal rem) C (mem j.val) (R.next j).width

def Move.ImageAt {d lanes D rem : ℕ} {A : State d lanes} (R : Move F A D rem)
    (C : SlotImage.Columns) (mem : ℕ → ℕ) (id : ℕ) : Prop :=
  ∀ j, j.val=id → SlotImage.Stored (R.next j).graph (R.next j).order (tagOrdinal rem) C mem (R.next j).width

private theorem at_degree {d l D D' r : ℕ} {A : State d l} (e : D=D') (R : Move F A D r)
    (C : SlotImage.Columns) (mem : ℕ → ℕ) (id : ℕ) (h : R.ImageAt C mem id) :
    (e ▸ R : Move F A D' r).ImageAt C mem id := by cases e; exact h

private theorem at_input {d i j D r : ℕ} (e : i=j) (A : State d i)
    (R : Move F (e ▸ A : State d j) D r) (C : SlotImage.Columns) (mem : ℕ → ℕ) (id : ℕ)
    (h : R.ImageAt C mem id) : (Move.recastInputLanes e A R).ImageAt C mem id := by cases e; exact h

private theorem images_degree {d l D D' r : ℕ} {A : State d l} (e : D=D') (R : Move F A D r)
    (C : SlotImage.Columns) (mem : ℕ → ℕ → ℕ) (h : R.Images C mem) :
    (e ▸ R : Move F A D' r).Images C mem := by cases e; exact h

private theorem images_input {d i j D r : ℕ} (e : i=j) (A : State d i)
    (R : Move F (e ▸ A : State d j) D r) (C : SlotImage.Columns) (mem : ℕ → ℕ → ℕ) (h : R.Images C mem) :
    (Move.recastInputLanes e A R).Images C mem := by cases e; exact h

section Raw
variable {d lanes rem s t D : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord s × BitWord t × BitWord rem)
    (P : PackingData A.Base (BitWord s) (BitWord t) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset)
    (hd : 0<d) (hD : 0<D) (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D ≤ 1/1024)
    (tagSize : 1<2^t) (code : Arc A.Base (BitWord s) (BitWord t) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ)

private theorem cfit (hd : 0<d) : 2≤2*d+1 := by omega

/-- A certificate has one slot image per true histogram branch, in the original
source numbering and with the balanced physical width, including zero padding. -/
def RawShrinkImages (C : SlotImage.Columns) (mem : ℕ → ℕ → ℕ) : Prop :=
  let n := parallel (2*d+1) d D
  let pad := padding (2*d+1) d D
  let cap := cfit hd
  let branches := shrinkBranches T A u P hd code
  ∀ j : Fin (Fintype.card branches),
    let len := issued T P (oldWidth A u) code cap ((Fintype.equivFin branches).symm j)
    let lay := ShrinkMotif.chooseWidths len
    let use := shrinkingGraph P lay n order cap binary_neg good
    let idle := tagPadding (V:=A.Base) (L:=BitWord rem) (adjacentMask tagSize) (adjacent_ne tagSize) pad
    let width := SlotRefinement.actualWidth (fun e=>n (typeIndex P binary_neg good lay e))
      (fun e : CrossEdge P lay=>len e.1 e.2) (allPieceSlots P binary_neg good lay n order cap pad)
    SlotImage.Stored (CompressorRefresh.union use idle) (productOrder A.order (tagOrdinal t))
      (tagOrdinal rem) C (mem j.val) width

def RawShrinkAt (C : SlotImage.Columns) (mem : ℕ → ℕ) (id : ℕ) : Prop :=
  let n := parallel (2*d+1) d D
  let pad := padding (2*d+1) d D
  let cap := cfit hd
  let branches := shrinkBranches T A u P hd code
  ∀ j : Fin (Fintype.card branches), j.val=id →
    let len := issued T P (oldWidth A u) code cap ((Fintype.equivFin branches).symm j)
    let lay := ShrinkMotif.chooseWidths len
    let use := shrinkingGraph P lay n order cap binary_neg good
    let idle := tagPadding (V:=A.Base) (L:=BitWord rem) (adjacentMask tagSize) (adjacent_ne tagSize) pad
    let width := SlotRefinement.actualWidth (fun e=>n (typeIndex P binary_neg good lay e))
      (fun e : CrossEdge P lay=>len e.1 e.2) (allPieceSlots P binary_neg good lay n order cap pad)
    SlotImage.Stored (CompressorRefresh.union use idle) (productOrder A.order (tagOrdinal t))
      (tagOrdinal rem) C mem width

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem shrinkMove_at (C : SlotImage.Columns) (mem : ℕ → ℕ) (id : ℕ)
    (h : RawShrinkAt T A u P good hd tagSize code order C mem id) :
    (shrinkMove T A u P agree good hd hD small tagSize code order).ImageAt C mem id := by
  unfold shrinkMove
  apply at_degree
  exact h

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem shrinkMove_images (C : SlotImage.Columns) (mem : ℕ → ℕ → ℕ)
    (h : RawShrinkImages T A u P good hd tagSize code order C mem) :
    (shrinkMove T A u P agree good hd hD small tagSize code order).Images C mem := by
  unfold shrinkMove
  apply images_degree
  exact h

end Raw

variable (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024)
    (A : State (2^s) (shrinkCharge s+rem))

abbrev shrinkRecordRoot :=
  let n := parallel (2*(2^s)+1) (2^s) D
  edgeOrder (shrinkRecordPacking s rem A) (baseNat (shrinkRecordState s rem A).order)
    (tagOrdinal (tagBits (2^s))).toEmbedding n (∑ j,n j)
    (fun i=>Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i))

private theorem tag_size : 1<2^(tagBits (2^s)) := by
  let d := 2^s
  have h := tagBits_fit d
  rw [show Fintype.card (BitWord (tagBits d))=2^(tagBits d) by simp [BitWord]] at h
  have pos : 0<d := Nat.two_pow_pos s
  have : 1≤2*d*((d+1)+(d+1)^2) :=
    Nat.mul_pos (Nat.mul_pos (by decide) pos) (by omega)
  exact lt_of_le_of_lt this h

private abbrev rawConditions (S : State (2^s) ((2*(2^s)+1)+(s+(tagBits (2^s)+rem)))) :=
  Ordered.binaryPacking_conditions S.order.symm S.graph

abbrev ShrinkBinaryImages (C : SlotImage.Columns) (mem : ℕ → ℕ → ℕ) :=
  let B := shrinkRecordState s rem A
  RawShrinkImages T B (shrinkRecordLane s rem) (shrinkRecordPacking s rem A)
    (rawConditions s rem B) (Nat.two_pow_pos s)
    (tag_size s) (shrinkRecordCode s rem A) (shrinkRecordRoot s D rem A) C mem

abbrev ShrinkBinaryAt (C : SlotImage.Columns) (mem : ℕ → ℕ) (id : ℕ) :=
  let B := shrinkRecordState s rem A
  RawShrinkAt T B (shrinkRecordLane s rem) (shrinkRecordPacking s rem A)
    (rawConditions s rem B) (Nat.two_pow_pos s)
    (tag_size s) (shrinkRecordCode s rem A) (shrinkRecordRoot s D rem A) C mem id

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem shrinkBinary_at (C : SlotImage.Columns) (mem : ℕ → ℕ) (id : ℕ)
    (h : ShrinkBinaryAt T s D rem A C mem id) :
    (shrinkBinary T s D rem hD small A).ImageAt C mem id := by
  unfold shrinkBinary
  apply at_input
  unfold shrinkRaw
  apply shrinkMove_at
  exact h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem shrinkBinary_images (C : SlotImage.Columns) (mem : ℕ → ℕ → ℕ)
    (h : ShrinkBinaryImages T s D rem A C mem) :
    (shrinkBinary T s D rem hD small A).Images C mem := by
  unfold shrinkBinary
  apply images_input
  unfold shrinkRaw
  apply shrinkMove_images
  exact h

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
