import OAI.ThreeFlat.Diagonal.CompressorDemandROM
import OAI.ThreeFlat.Diagonal.CompressorDenseMotifs
import OAI.ThreeFlat.Diagonal.CompressorStageAddress
import OAI.ThreeFlat.Diagonal.CompressorShiftSlices
import OAI.ThreeFlat.Diagonal.SlotImage

namespace OAI
/-! # Reading the old physical width image through a shrinking lane decomposition -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Demand
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast

section Ordinals
variable {B H : Type*} [AddCommGroup H] {N w n d c t l : ℕ}
variable (P : PackingData B H (BitWord t) (BitWord l) d c)

def laneDigits : (BitWord c × H × BitWord t × BitWord l) ≃ ((BitWord l × BitWord t) × H) × BitWord c where
  toFun a := (((a.2.2.2,a.2.2.1),a.2.1),a.1)
  invFun a := (a.2,a.1.2,a.1.1.2,a.1.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

def laneOrdinal : (BitWord c × H × BitWord t × BitWord l) ≃ Fin (2^l*2^t*d*2^c) :=
  let upper := ((tagOrdinal l).prodCongr (tagOrdinal t)).trans finProdFinEquiv
  let withSlot := (upper.prodCongr P.slotLabel).trans finProdFinEquiv
  laneDigits.trans ((withSlot.prodCongr (tagOrdinal c)).trans finProdFinEquiv)

omit [AddCommGroup H] in
theorem edge_address (base : B ≃ Fin N) (a : Arc B H (BitWord t) (BitWord l) d c) :
    SlotImage.edgeOrdinal base (laneOrdinal P) (packedAddress.symm a)=key P (baseNat base) a := by
  rw [demandOrdinal_formula]
  change ((base a.1.1.1).val*d+a.1.2.val)*(2^l*2^t*d*2^c) +
    ((tagOrdinal c a.2.1).val+2^c*((P.slotLabel a.2.2).val+d*((tagOrdinal t a.1.1.2.1).val+2^t*(tagOrdinal l a.1.1.2.2).val))) = _
  rfl

theorem split_lane_ordinal {s : ℕ}
    (P : PackingData B (BitWord s) (BitWord t) (BitWord l) (2^s) c)
    (label : ∀u,(P.slotLabel u).val=(tagOrdinal s u).val) (x : BitWord (c+(s+(t+l)))) :
    (laneOrdinal P (laneSplit c s t l x)).val = (tagOrdinal _ x).val := by
  rw [ordinal_split x,ordinal_split (splitWord c _ x).2,
    ordinal_split (splitWord s _ (splitWord c _ x).2).2]
  let a := laneSplit c s t l x
  change (tagOrdinal c a.1).val+2^c*((P.slotLabel a.2.1).val+
    2^s*((tagOrdinal t a.2.2.1).val+2^t*(tagOrdinal l a.2.2.2).val)) = _
  rw [label]
  rfl

end Ordinals

variable {B H : Type} [AddCommGroup H] {N w n d c t l : ℕ}
variable {P : PackingData B H (BitWord t) (BitWord l) d c}
omit [AddCommGroup H] in
theorem widths_from_image (base : B ≃ Fin N) (E : Codec B w c t l) (C : SlotImage.Columns)
    (pub : Param → Word w) (mem : Memory w) (vs : Fin n → Word w)
    (widths : Arc B H (BitWord t) (BitWord l) d c → ℕ)
    (stored : SlotImage.Stored (StageAddress.packedGraph P) base (laneOrdinal P) C (fun a => (mem a).val)
      (fun z => widths (packedAddress z)))
    (table tagCount laneCount : Formula n) (bt : table.value pub mem vs = (C.widths:Word w))
    (bv : ∀v,E.base v=((base v).val:Word w)) (tt : tagCount.value pub mem vs=((2^t:ℕ):Word w))
    (lt : laneCount.value pub mem vs=((2^l*2^t*d*2^c:ℕ):Word w))
    (bounds : C.widths+N*d*(2^l*2^t*d*2^c)≤2^w) :
    WidthReads P E (baseNat base) pub mem vs table tagCount laneCount widths := by
  have safe (a : Arc B H (BitWord t) (BitWord l) d c) :
      C.widths+key P (baseNat base) a<2^w := by
    rw [←edge_address P base a]
    exact (Nat.add_lt_add_left (SlotImage.edgeOrdinal_lt base (laneOrdinal P) (packedAddress.symm a)) _).trans_le bounds
  refine ⟨bv,tt,lt,fun a => (Nat.le_add_left ..).trans_lt (safe a),?_⟩
  intro a
  have hv := stored.widthWord (packedAddress.symm a)
  rw [edge_address,Equiv.apply_symm_apply] at hv
  rw [bt,←Nat.cast_add,Fin.val_cast_of_lt (safe a),←hv,Fin.cast_val_eq_self]


end ThreeFlat.Diagonal.CompressorPacking.Native.Demand

end OAI
