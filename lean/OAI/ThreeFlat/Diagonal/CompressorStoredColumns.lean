import OAI.ThreeFlat.Diagonal.CompressorStoredWidths
import OAI.ThreeFlat.Diagonal.CompressorStageHeader

namespace OAI
/-! # Reading the split displacement fields of a numbered old graph -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.StoredColumns

open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Placement
open scoped Fin.NatCast
section Ordinals
variable {B H : Type*} {c d t l N w : ℕ} [AddCommGroup H]
variable (P : PackingData B H (BitWord t) (BitWord l) d c)

def digit (c d t field x : ℕ) : ℕ :=
  let y := x/2^c
  let z := y/d
  if field=0 then x%2^c else if field=1 then y%d else if field=2 then z%2^t else z/2^t

def shiftField (p : B × Fin d) (back : Bool) (f : Fin 4) : ℕ :=
  let q := if back then P.slots.target.symm p else p
  ![(tagOrdinal c (P.bitShift q)).val,(P.slotLabel (P.slotShift q)).val,
    (tagOrdinal t (P.siteShift q).1).val,(tagOrdinal l (P.siteShift q).2).val] f

private theorem split_lo {k a : ℕ} (h : a<k) (b : ℕ) : (a+k*b)%k=a := by
  simp [Nat.add_mod,Nat.mod_eq_of_lt h]

private theorem split_hi {k a : ℕ} (h : a<k) (b : ℕ) : (a+k*b)/k=b := by
  rw [Nat.add_comm,Nat.mul_add_div (by omega : 0<k),Nat.div_eq_of_lt h,Nat.add_zero]

omit [AddCommGroup H] in
theorem digit_lane (u : BitWord c × H × BitWord t × BitWord l) (f : Fin 4) :
    digit c d t f.val (Demand.laneOrdinal P u).val =
      ![(tagOrdinal c u.1).val,(P.slotLabel u.2.1).val,
        (tagOrdinal t u.2.2.1).val,(tagOrdinal l u.2.2.2).val] f := by
  let a := (tagOrdinal c u.1).val
  let b := (P.slotLabel u.2.1).val
  let z := (tagOrdinal t u.2.2.1).val
  let h := (tagOrdinal l u.2.2.2).val
  have av : a<2^c := (tagOrdinal c _).isLt
  have bv : b<d := (P.slotLabel _).isLt
  have zv : z<2^t := (tagOrdinal t _).isLt
  have packed : (Demand.laneOrdinal P u).val = a+2^c*(b+d*(z+2^t*h)) := rfl
  rw [packed]
  fin_cases f <;> simp [digit,split_lo av,split_hi av,split_lo bv,split_hi bv,
    split_lo zv,split_hi zv,a,b,z,h]

end Ordinals

variable {B H : Type} {c d t l N w : ℕ} [AddCommGroup H]
variable (P : PackingData B H (BitWord t) (BitWord l) d c)

omit [AddCommGroup H] in
theorem stored_slice (base : B ≃ Fin N) (C : SlotImage.Columns) (mem : ℕ → ℕ)
    (width : SlotImage.Edge B (BitWord c × H × BitWord t × BitWord l) d → ℕ)
    (stored : SlotImage.Stored (StageAddress.packedGraph P) base (Demand.laneOrdinal P) C mem width)
    (p : B × Fin d) (back : Bool) (f : Fin 4) :
    digit c d t f.val (mem (SlotImage.cell C base p back 2)) = shiftField P p back f := by
  rw [stored.displacement]
  exact digit_lane P _ _

/-- Contiguous slice read needed by the thirteen column projection record. -/
theorem word_slot (m : Memory w) (a b i d : ℕ) (fit : a+(b*d+i)<2^w) :
    slot (words m) d (a:Word w) (b:Word w) (i:Word w) = m (a+(b*d+i)) := by
  change m ((a:Word w)+((b:Word w)*(d:Word w)+(i:Word w))).val = _
  apply congrArg m
  change (a%2^w+(((b%2^w*(d%2^w))%2^w+i%2^w)%2^w))%2^w=a+(b*d+i)
  rw [←Nat.mul_mod b d (2^w), ←Nat.add_mod (b*d) i (2^w),
    ←Nat.add_mod a (b*d+i) (2^w), Nat.mod_eq_of_lt fit]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.StoredColumns

end OAI
