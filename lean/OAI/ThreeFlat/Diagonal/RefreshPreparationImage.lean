import OAI.ThreeFlat.Diagonal.RefreshSplitImage
import OAI.ThreeFlat.Diagonal.RefreshSparseImage
import OAI.ThreeFlat.Diagonal.RefreshStageRuns

namespace OAI
/-! # Exact histogram descriptor table produced by the complete refresh preparation -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan
open RefreshDemandRows RefreshTies CompressorPacking.Native MotifIntegerChoice
open scoped Classical Fin.CommRing
noncomputable section

variable {W v a t k : ℕ} (current : Word W) (m : Memory W)

structure PreparationLayout (v a t : ℕ) (C : SlotImage.Columns) (split desc : ℕ) : Prop where
  header : (m current.val).val+19<2^W
  remain : info (fun i => (m i).val) current 8=2^t
  width : info (fun i => (m i).val) current 9=C.widths
  graph : info (fun i => (m i).val) current 10=C.graph
  rows : info (fun i => (m i).val) current 11=C.rows
  shifts : info (fun i => (m i).val) current 12=split
  length : info (fun i => (m i).val) current 13=3*C.rows
  choices : info (fun i => (m i).val) current 2=desc
  choiceLen : info (fun i => (m i).val) current 18=3*(v*2^t)
  graphCap : C.graph+6*C.rows≤2^W
  widthCap : C.widths+v*mPort a*(mPort a*2^t)≤2^W
  shiftCap : split+3*C.rows<2^W
  choiceCap : desc+3*(v*2^t)<2^W
  outsideShift : ∀ i,i=current.val ∨ (m current.val).val≤ i ∧ i≤(m current.val).val+19 ∨
      C.graph≤ i ∧ i<C.graph+6*C.rows ∨ C.widths≤ i ∧ i<C.widths+v*mPort a*(mPort a*2^t) →
      apart split (3*C.rows) i
  outsideChoice : ∀ i,sourceCell current.val (m current.val).val C split (v*mPort a*(mPort a*2^t)) i →
      apart desc (3*(v*2^t)) i

attribute [local irreducible] choiceWords splitShifts descriptorWord

theorem preparation_image (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (C : SlotImage.Columns) (split desc : ℕ) (w : SlotImage.RefreshInput v a t → ℕ)
    (image : SlotImage.Stored G (Equiv.refl _) (SlotImage.pairLane (tagOrdinal a) (tagOrdinal t)) C (fun i => (m i).val) w)
    (z : PreparationLayout current m v a t C split desc)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ) (size : Fin (k+1) → ℕ)
    (radix : mPort a<2^W) (lanes : 2^t<2^W) (entries : k+1≤2^W)
    (tileFit : ∀ z j i,sentinel (fun e=>SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm) z e))
      +base j i<2^W) :
    let o := (preparation current base size).run m
    Source current o G C split w ∧ ∀ (u : Block v t) (j : Fin 3),
      o (desc+(blockId u*3+j.val))=(descriptorWord G w base size (u,j):Word W) := by
  let m1 := (Pipeline.scan current 12 13 (closed (splitShifts (mPort a) current))).run m
  let m2 := (Pipeline.scan current 2 18 (closed (choiceWords current base size))).run m1
  have eq1 : m1=fillSegment split (3*C.rows) (separated m C split (mPort a)) m := by
    apply split_run current m C split _ radix (by have := z.header; omega) z.graph z.rows z.shifts z.length
      z.graphCap z.shiftCap
    intro i hi
    rcases hi with h|h|h
    · exact z.outsideShift i (.inl h)
    · exact z.outsideShift i (.inr (.inl ⟨h.1,by omega⟩))
    · exact z.outsideShift i (.inr (.inr (.inl h)))
  have keep1 (i : ℕ) (h : apart split (3*C.rows) i) : m1 i=m i := by
    rw [eq1]
    exact segment_other m _ _ _ _ h
  have ptr := keep1 _ (z.outsideShift _ (.inl rfl))
  have hdr (j : ℕ) (hj : j≤19) := info_frame current m 19 (m':=m1)
    (fun i hi=>keep1 i (z.outsideShift i (hi.imp_right Or.inl))) j hj
  have image1 : SlotImage.Stored G (Equiv.refl _) (SlotImage.pairLane (tagOrdinal a) (tagOrdinal t)) C
      (fun i=>(m1 i).val) w := by
    apply image.frame
    · intro i lo hi
      exact congrArg Fin.val (keep1 i (z.outsideShift i (.inr (.inr (.inl ⟨lo,hi⟩)))))
    · intro i lo hi
      exact congrArg Fin.val (keep1 i (z.outsideShift i (.inr (.inr (.inr ⟨lo,hi⟩)))))
  have shifts1 : SlotImage.SplitColumns C split (fun i=>(m1 i).val) v a := by
    rw [eq1]
    exact split_image m image (fun i lo hi=>z.outsideShift i (.inr (.inr (.inl ⟨lo,hi⟩))))
  have source1 : Source current m1 G C split w := ⟨image1,shifts1,by rw [ptr]; exact z.header,
    (hdr 8 (by decide)).trans z.remain,(hdr 9 (by decide)).trans z.width,(hdr 10 (by decide)).trans z.graph,
    (hdr 11 (by decide)).trans z.rows,(hdr 12 (by decide)).trans z.shifts,z.graphCap,z.widthCap,z.shiftCap.le⟩
  have eq2 : m2=fillSegment desc (3*(v*2^t))
      (tableWord (choices (a:=a)) desc (fun q=>(descriptorWord G w base size q:Word W))) m1 := by
    apply choice_run current m1 G C split desc w source1 base size ((hdr 2 (by decide)).trans z.choices)
      ((hdr 18 (by decide)).trans z.choiceLen) z.choiceCap lanes radix.le entries tileFit
    simpa only [ptr,apart] using z.outsideChoice
  change Source current m2 G C split w ∧ ∀ (u : Block v t) (j : Fin 3),
    m2 (desc+(blockId u*3+j.val))=(descriptorWord G w base size (u,j):Word W)
  constructor
  · apply source1.frame m2
    intro i hi
    rw [ptr] at hi
    rw [eq2]
    exact segment_other m1 _ _ _ _ (z.outsideChoice i hi)
  · intro u j
    have address : (choices (a:=a) (u,j)).val = blockId u*3+j.val :=
      RefreshStageLayout.descriptor_index (h:=0) (pad:=0) (m:=mPort a) u j
    have rd := scan_read m1 (choices (a:=a)) (fun q=>(descriptorWord G w base size q:Word W)) desc (u,j)
    rw [address] at rd
    exact (congrFun eq2 (desc+(blockId u*3+j.val))).trans rd


end
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
