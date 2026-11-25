import OAI.ThreeFlat.Diagonal.NavigationArchive
import OAI.ThreeFlat.RAM.HeaderScanLayout
import OAI.ThreeFlat.Diagonal.CompressorHalfFits
import OAI.ThreeFlat.Diagonal.SlotImageViews

namespace OAI
/-! # Stored source, side, width and prefix in the initial cursor metadata -/
namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalPinsExpr
open CompressorPacking.Native CompressorPacking.Native.ShrinkStage.Halves
open scoped Fin.CommRing
variable {W t : ℕ} {B : Type} (A : Archive) (m : Memory W)
local notation "d" => A.initialDegree
local notation "C" => SlotImage.Columns.mk A.cursor.graph (A.axes*d) A.cursor.width
local notation "N" => fun i => Fin.val (m i)

private theorem pair_lt {a b n r : ℕ} (ha : a<n) (hb : b<r) : a*r+b<n*r := by
  calc a*r+b < a*r+r := Nat.add_lt_add_left hb _
       _=(a+1)*r := (Nat.succ_mul ..).symm
       _≤n*r := Nat.mul_le_mul_right r ha

theorem initialHalf_word (H : Scans.Header (A.control:Word W) m A.seed 63 A.seedWords)
    (G : LiftedSlots B d (BitWord t)) (base : B ≃ Fin A.axes)
    (width : SlotImage.Edge B (BitWord t) d → ℕ)
    (stored : SlotImage.Stored G base (tagOrdinal t) C N width)
    (lanes : A.remainingLanes=2^t) (controlRoom : A.control<2^W)
    (degreeRoom : 2*d<2^W) (laneRoom : 2^t<2^W)
    (graphRoom : A.cursor.graph+6*(A.axes*d)≤2^W)
    (widthRoom : A.cursor.width+(A.axes*d)*2^t≤2^W)
    (recordRoom : A.seedWords 11+A.seedWords 12≤2^W)
    (u : B × BitWord t) (j : Fin (2*d)) (col : Fin 4) :
    let i:=(siteNumber base u*(2*d)+j.val)*4+col.val
    let e:=sourceHalf G u j
    Formula.value (fun _=>0) m (fun _ : Fin 1=>((A.seedWords 11+i:ℕ):Word W)) A.initialHalf=
      ((![edgeNumber base e,if j.val<d then 0 else 1,width e,prefixValue G width u j] : Fin 4→ℕ) col:Word W) := by
  let i:=(siteNumber base u*(2*d)+j.val)*4+col.val
  let vs:=fun _ : Fin 1=>((A.seedWords 11+i:ℕ):Word W)
  let vals:=fun j=>(vs j).val
  let data:=fun _ : Param=>0
  let V:=Formula.natural W data N vals
  let Fit:=Formula.Fits W data N vals
  let slots:=Formula.op .mul (A.initialField 4) (A.initialField 5)
  let q : HalfColumns := ⟨A.initialField 6,A.initialField 0,slots,A.initialField 2⟩
  let pos:=A.initialOffset 11
  have oldHead : (m A.control).val=A.seed := by simpa only [Fin.val_cast_of_lt controlRoom] using H.pointer
  have natural (j : ℕ) (small : j≤63) : V (A.initialField j)=A.seedWords j := by
    change (m ((m A.control).val+j)).val=_
    rw [oldHead]; exact H.values _ small
  have safe (j : ℕ) (small : j≤63) : Fit (A.initialField j) := by
    refine ⟨⟨⟨trivial,controlRoom⟩,trivial,trivial⟩,?_⟩
    change (m A.control).val+j<2^W
    rw [oldHead];have:=H.fit;omega
  have rows : V slots=A.axes*d := by
    change V (A.initialField 4)*V (A.initialField 5)=_
    rw [natural 4 (by decide),natural 5 (by decide)];rfl
  have cols : q.layout V=⟨2^t,(C).graph,(C).rows,(C).widths⟩ := by
    change Layout.mk (V (A.initialField 6)) (V (A.initialField 0)) (V slots) (V (A.initialField 2))=_
    rw [natural 6 (by decide),natural 0 (by decide),rows,natural 2 (by decide)]
    change Layout.mk A.remainingLanes A.cursor.graph (A.axes*d) A.cursor.width=
      Layout.mk (2^t) A.cursor.graph (A.axes*d) A.cursor.width
    rw [lanes]
  have st : Stored G base (q.layout V) N width := cols.symm ▸ SlotImage.forHalves stored
  have rg : Region (W:=W) data N vals q A.axes d t := by
    refine ⟨⟨safe 6 (by decide),safe 0 (by decide),⟨safe 4 (by decide),safe 5 (by decide),trivial⟩,
      safe 2 (by decide)⟩,rows,?_,?_,degreeRoom,laneRoom⟩
    · change V (A.initialField 0)+6*(A.axes*d)≤_
      rw [natural 0 (by decide)];exact graphRoom
    · change V (A.initialField 2)+(A.axes*d)*2^t≤_
      rw [natural 2 (by decide)];exact widthRoom
  have inFile : i<A.seedWords 12 := by
    have site := pair_lt (base u.1).isLt (tagOrdinal t u.2).isLt
    have r:=pair_lt (pair_lt site j.isLt) col.isLt
    change (siteNumber base u*(2*d)+j.val)*4+col.val<8*d*(A.axes*A.remainingLanes)
    rw [lanes]
    change (siteNumber base u*(2*d)+j.val)*4+col.val < ((A.axes*2^t)*(2*d))*4 at r
    convert r using 1; ring
  have room : A.seedWords 11+i<2^W := (Nat.add_lt_add_left inFile _).trans_le recordRoom
  have address : vals 0=A.seedWords 11+i := Fin.val_cast_of_lt room
  have index : V pos=i := by
    change vals 0-V (A.initialField 11)=_
    rw [address,natural 11 (by decide)];omega
  have sourceEnd : V (A.initialField 11)<2^W := by
    rw [natural 11 (by decide)]
    exact (Nat.le_add_right _ i).trans_lt room
  have posFit : Fit pos := ⟨trivial,safe 11 (by decide),(vs 0).isLt,sourceEnd⟩
  have ix : V pos<2^W := by rw [index];omega
  have small : 4<2^W := by have:=H.fit;omega
  have checked:=record_fits data N vals q st rg pos u j col posFit ix small index
  have read:=record_read W data N vals q st pos u j col index
  have word:=Formula.value_eq_natural (record q d pos) data N vals checked
  change Formula.value (fun _=>0) m vs (record q d pos)=_
  simpa only [data,vals,Nat.cast_zero,Fin.cast_val_eq_self,read] using word

end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
