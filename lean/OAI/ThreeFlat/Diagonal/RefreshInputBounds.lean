import OAI.ThreeFlat.Diagonal.RefreshSplitNative
import OAI.ThreeFlat.Diagonal.SlotImageViews

namespace OAI
/-! # Refresh inputs decoded from the shared physical stage image -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows CompressorPacking.Native
open RefreshDemandRows

set_option quotPrecheck false

variable {W v a t : ℕ} (current : Word W) (m : Memory W) (vs : Fin 1 → Word W)
local notation "N" => fun i => (m i).val
local notation "U" => fun (i : Fin 1) => (vs i).val
local notation "V" => Formula.natural W (fun _ => 0) N U
local notation "Fit" => Formula.Fits W (fun _ => 0) N U

/-- Only numerical layout bounds and data present in the predecessor image.
The width and coordinate programs share these bounds. -/
structure Source (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (C : SlotImage.Columns) (split : ℕ) (w : SlotImage.RefreshInput v a t → ℕ) : Prop where
  image : SlotImage.Stored G (Equiv.refl _) (SlotImage.pairLane (tagOrdinal a) (tagOrdinal t)) C N w
  shifts : SlotImage.SplitColumns C split N v a
  headerBound : (m current.val).val+19<2^W
  remaining : info N current 8 = 2^t
  width : info N current 9 = C.widths
  graph : info N current 10 = C.graph
  rows : info N current 11 = C.rows
  splitBase : info N current 12 = split
  graphBound : C.graph+6*C.rows≤2^W
  widthBound : C.widths+v*mPort a*(mPort a*2^t)≤2^W
  shiftsBound : split+3*C.rows≤2^W

variable {current m} {G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t)}
    {C : SlotImage.Columns} {split : ℕ} {w : SlotImage.RefreshInput v a t → ℕ}
    (s : Source current m G C split w)

include s

theorem Source.columns : (input current).map V=SlotImage.demandColumns C split := by
  have width := s.width
  have graph := s.graph
  have rows := s.rows
  have shifts := s.splitBase
  change Columns.mk (info N current 9) (info N current 10+info N current 11*3)
    (info N current 10+info N current 11*4) (info N current 12+info N current 11*2)
    (info N current 12+info N current 11*1)=_
  rw [width,graph,rows,shifts,Nat.mul_one]
  rfl

theorem Source.demand : Stored G ((input current).map V) N (SlotImage.demandWidth w) := by
  rw [s.columns vs]
  exact SlotImage.demandStored s.image s.shifts

theorem Source.formulas : Fit (input current).widths ∧ Fit (input current).sourceBase ∧
    Fit (input current).sourceSlot ∧ Fit (input current).portShift ∧ Fit (input current).laneShift := by
  have b := s.headerBound
  have pair (src i : ℕ) (h : src≤19) :
      Fit (plus (field current src) (.op .mul (field current 11) (.lit i))) :=
    ⟨field_fit current m vs _ (by omega),⟨field_fit current m vs _ (by omega),trivial,trivial⟩,trivial⟩
  exact ⟨field_fit current m vs 9 (by omega),pair 10 3 (by decide),pair 10 4 (by decide),
    pair 12 2 (by decide),pair 12 1 (by decide)⟩

theorem Source.widthRegion : V (input current).widths+(v*mPort a)*(mPort a*2^t)≤2^W := by
  change info N current 9+_≤_
  rw [s.width]
  exact s.widthBound

theorem Source.columnRegions (c : Formula 1) (inList : c∈[(input current).sourceBase,(input current).sourceSlot,
    (input current).portShift,(input current).laneShift]) : V c+v*mPort a≤2^W := by
  have b := s.shiftsBound
  have g := s.graphBound
  have q := s.image.rowCount
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inList
  rcases inList with rfl|rfl|rfl|rfl
  · change info N current 10+info N current 11*3+_≤_
    rw [s.graph,s.rows,←q]; omega
  · change info N current 10+info N current 11*4+_≤_
    rw [s.graph,s.rows,←q]; omega
  · change info N current 12+info N current 11*2+_≤_
    rw [s.splitBase,s.rows,←q]; omega
  · change info N current 12+info N current 11*1+_≤_
    rw [s.splitBase,s.rows,←q]; omega

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
