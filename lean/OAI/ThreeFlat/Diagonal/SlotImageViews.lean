import OAI.ThreeFlat.Diagonal.SlotImage
import OAI.ThreeFlat.Diagonal.CompressorHalfValues
import OAI.ThreeFlat.Diagonal.RefreshDemandRows
import OAI.ThreeFlat.Diagonal.CompressorLaneSplit

namespace OAI
/-! # Lane changes and numerical consumers of the common graph image -/

namespace ThreeFlat.Diagonal.SlotImage

open Computability.VPVNP.Compression CompressorPacking CompressorPacking.Native RefreshDemandRows

variable {B H L L' : Type} {v m r d : ℕ}

/-- Retain the same old numerical image while changing the additive chart on lanes. -/
theorem changeLanes_stored [AddCommGroup L] [AddCommGroup L'] {G : LiftedSlots B d L}
    {base : B ≃ Fin v} {lane : L ≃ Fin r} {C : Columns} {mem : ℕ → ℕ} {w : Edge B L d → ℕ}
    (old : Stored G base lane C mem w) (u : L ≃+ L') :
    Stored (changeLanes G u) base (u.symm.toEquiv.trans lane) C mem (fun e => w (e.1,u.symm e.2)) where
  rowCount := old.rowCount
  graph p back f := by
    rw [old.graph]
    cases back <;> fin_cases f <;> simp [fields,oriented,shift,changeLanes]
  widthWord e := old.widthWord (e.1,u.symm e.2)

/-- The coordinate consumed at this stage lies in the low part of the old
binary lane ordinal; the residual lane is the high part. -/
def pairLane (port : H ≃ Fin m) (lane : L ≃ Fin r) : H × L ≃ Fin (m*r) :=
  (((Equiv.prodComm H L).trans (lane.prodCongr port)).trans finProdFinEquiv).trans (finCongr (Nat.mul_comm r m))

theorem pairLane_val (port : H ≃ Fin m) (lane : L ≃ Fin r) (p : H × L) :
    (pairLane port lane p).val=(port p.1).val+m*(lane p.2).val := rfl

theorem forHalves {t : ℕ} {G : LiftedSlots B d (BitWord t)} {base : B ≃ Fin v} {C : Columns}
    {mem : ℕ → ℕ} {w : Edge B (BitWord t) d → ℕ} (s : Stored G base (tagOrdinal t) C mem w) :
    ShrinkStage.Halves.Stored G base ⟨2^t,C.graph,C.rows,C.widths⟩ mem w where
  lanes := rfl
  srcBase p := s.neighbor p true
  srcSlot p := s.mate p true
  disp p := s.displacement p true
  widthWord e := s.widthWord e

variable {a t : ℕ}
abbrev RefreshInput (v a t : ℕ) := Edge (Fin v) (BitWord a × BitWord t) (2^a)

def demandWidth (w : RefreshInput v a t → ℕ) (p : Address' v a t) :=
  w ((p.1.1,p.2.2), (tagOrdinal a).symm p.2.1,p.1.2)

def demandColumns (C : Columns) (split : ℕ) : RefreshDemandRows.Columns ℕ :=
  ⟨C.widths,C.graph+C.rows*3,C.graph+C.rows*4,split+C.rows*2,split+C.rows⟩

/-- Three newly emitted shift columns, defined entirely by the packed input
graph. Their order is forward residual, reverse residual, reverse consumed. -/
structure SplitColumns (C : Columns) (split : ℕ) (mem : ℕ → ℕ) (v a : ℕ) : Prop where
  forward : ∀ p : Fin v × Fin (2^a), mem (split+ordinal (Equiv.refl _) p)=
    mem (cell C (Equiv.refl _) p false 2)/2^a
  reverse : ∀ p : Fin v × Fin (2^a), mem (split+C.rows+ordinal (Equiv.refl _) p)=
    mem (cell C (Equiv.refl _) p true 2)/2^a
  consumed : ∀ p : Fin v × Fin (2^a), mem (split+C.rows*2+ordinal (Equiv.refl _) p)=
    mem (cell C (Equiv.refl _) p true 2)%2^a

theorem demandStored {G : LiftedSlots (Fin v) (2^a) (BitWord a × BitWord t)}
    {C : Columns} {mem : ℕ → ℕ} {w : RefreshInput v a t → ℕ} {split : ℕ}
    (image : Stored G (Equiv.refl _) (pairLane (tagOrdinal a) (tagOrdinal t)) C mem w)
    (divided : SplitColumns C split mem v a) :
    RefreshDemandRows.Stored G (demandColumns C split) mem (demandWidth w) where
  width e := by
    let p : RefreshInput v a t := ((e.1.1,e.2.2), (tagOrdinal a).symm e.2.1,e.1.2)
    have h := image.widthWord p
    simpa [p,demandWidth,demandColumns,edgeOrdinal,ordinal,RefreshDemandRows.index,
      RefreshDemandRows.ordinal,pairLane_val] using h
  src i j := image.neighbor (i,j) true
  slot i j := image.mate (i,j) true
  consumed i j := by
    rw [show mem ((demandColumns C split).portShift+(i.val*mPort a+j.val))=_ from divided.consumed (i,j),
      image.displacement (i,j) true,pairLane_val]
    exact (Nat.add_mul_mod_self_left ..).trans (Nat.mod_eq_of_lt (tagOrdinal a _).isLt)
  remaining i j := by
    rw [show mem ((demandColumns C split).laneShift+(i.val*mPort a+j.val))=_ from divided.reverse (i,j),
      image.displacement (i,j) true,pairLane_val]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt (tagOrdinal a _).isLt,Nat.zero_add]
    rfl

end ThreeFlat.Diagonal.SlotImage

end OAI
