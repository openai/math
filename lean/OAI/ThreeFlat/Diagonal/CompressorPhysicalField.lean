import OAI.ThreeFlat.Diagonal.CompressorPostRows
import OAI.ThreeFlat.Diagonal.CompressorArcImage

namespace OAI
/-! # The graph-row update returns the six fields of the complete regular successor -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement Graph
open scoped BigOperators Classical Fin.NatCast

def tagNumber {B : Type*} {N t : ℕ} (b : B ≃ Fin N) :
    B × BitWord t ≃ Fin (N*2^t) := (b.prodCongr (tagOrdinal t)).trans finProdFinEquiv

theorem tagNumber_val {B : Type*} {N t : ℕ} (b : B ≃ Fin N) (v : B × BitWord t) :
    (tagNumber b v).val=(b v.1).val*2^t+(tagOrdinal t v.2).val := by
  change _+_*_=_*_+_
  ac_rfl

def graphField : Fin 3 → Graph.Field := ![.neighbor,.matePort,.delta]

variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l : ℕ}
variable (cell : Word w) (pub : Fin 1 → Word w) (m : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value (fun _=>cell) m vs
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (E : Codec B w S.colors t l) (R : ArcReads P E ((oldColumns (Demand.formulaOps 1) ptr).map (Formula.value (fun _ => cell) m vs)) m)
variable (hb : ∀z,E.base z=((b z).val:Word w)) (hi : Function.Injective E.base)
variable (bound : ∀i,S.pieces i≤S.pieceRadix) (fit : ∀e,edgeId S P (baseNat b) bound e<2^w)
variable (lay : Bool) (colors : 2≤S.colors) (good : TagConditions P.slots (shift P) P.offset)


include hb in
omit [Fintype B] in
theorem packed_word (v : B × BitWord t) :
    baseAddress S E v = ((tagNumber b v).val:Word w) := by
  simp only [baseAddress,hb,tagNumber_val,Nat.cast_add,Demand.tag_cast E.tags v.2]
  apply congrArg (fun n : Word w => n + tagWord E.tags v.2)
  apply Fin.ext
  exact (Nat.mul_mod (b v.1).val (2^t) (2^w)).symm

set_option maxHeartbeats 2400000 in
include pub R hb hi fit in
theorem physical_live (one : (1:Word w)≠0)
    (rad : (radices o ptr S).map V = rowRadices (w:=w) (t:=t) (l:=l) S)
    (cap : liveDegree S≤2^w) (tagsFit : 2^t<2^w)
    (basesFit : ∀v : B × BitWord t,(E.base v.1).val*2^t+(tagOrdinal t v.2).val<2^w)
    (rev : Bool) (p : (B × BitWord t) × Fin (liveDegree S)) (f : Fin 3) (dest : F)
    (bv : V (.op .div (.op .sub (.reg 0) dest) (.lit S.outputDegree))=baseAddress S E p.1)
    (iv : V (.op .mod (.op .sub (.reg 0) dest) (.lit S.outputDegree))=(p.2.val:Word w))
    (live : (p.2.val:Word w)<(S.liveDegree:Word w))
    {pad : ℕ} (extra : LiftedSlots (B × BitWord t) pad (BitWord l)) :
    V (update S lay rev (graphField f) dest)=
      ((SlotImage.fields (CompressorRefresh.union (shrinkingGraph P lay S.pieces
        (edgeOrder P (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) colors binary_neg good) extra) (tagNumber b) (tagOrdinal l)
        (CompressorRefresh.leftRow p) rev f):Word w) := by
  rw [CompressorRefresh.fields_left]
  have h (j : Fin 3) := retained_field cell pub m vs S P E R (baseNat b) hb hi bound fit lay colors good one rad cap
    tagsFit basesFit rev p (graphField j) dest bv iv live
  revert f
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))
  · exact (h 0).trans (packed_word S b E hb _)
  · exact h 1
  · exact (h 2).trans (Demand.tag_cast E.lanes _).symm


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
