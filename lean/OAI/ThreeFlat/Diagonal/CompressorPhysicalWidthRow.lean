import OAI.ThreeFlat.Diagonal.CompressorPhysicalKeyRow
import OAI.ThreeFlat.Diagonal.CompressorPhysicalWidth
import OAI.ThreeFlat.Diagonal.CompressorKeyImage

namespace OAI
/-! # Selected subdivision width at an absolute source-slot/lane address -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement Graph
open scoped Classical Fin.NatCast
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l pad : ℕ}
variable (cell : Word w) (m : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value (fun _=>cell) m vs
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors) (b : B ≃ Fin N)
variable (bound : ∀i,S.pieces i≤S.pieceRadix) (lay : Bool) (hc : 2≤S.colors)
variable (good : TagConditions P.slots (shift P) P.offset)
variable (E : Codec B w S.colors t l) (R : ArcReads P E ((oldColumns (Demand.formulaOps 1) ptr).map (Formula.value (fun _ => cell) m vs)) m)
variable (prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ)
variable (W : Demand.WidthReads P E (baseNat b) (fun _=>cell) m vs (f oldWidths) (f tags) (f oldLanes) prior)
variable (supply : P.Motif → Fin 8 → ℕ)
local notation "tagged" => tagNumber (t:=t) b

theorem cut_index (start k : ℕ) (dest : F) (top : start+k<2^w)
    (origin : V dest=(start:Word w)) (here : vs 0=((start+k:ℕ):Word w)) :
    V (.cut (.reg 0) dest)=(k:Word w) := by
  change (if Comparison.lt.test (vs 0) (V dest) then _ else BinaryOp.sub.eval (vs 0) (V dest))=_
  rw [here,origin,test_cast .lt _ _ top (by omega)]
  have h : ¬start+k<start := by omega
  simp only [natTest,h,decide_false,ite_false,Bool.false_eq_true]
  change ((start+k:ℕ):Word w)-(start:Word w)=_
  rw [Nat.cast_add]
  abel

theorem output_chosen (S : Stage) (lay : Bool) (chosen : V (f selected)=if lay then 1 else 0)
    (one : (1:Word w)≠0) :
    V (output S)=V (ShrinkWidth.output g (widthLayout ptr S) S lay (f keys) (f issued)
      (f remaining) (.cut (.reg 0) (f nextWidths))) := by
  cases lay <;> simp [output,Formula.value,Comparison.test,chosen,Ne.symm one]

include R W in
theorem physical_width_read (chosen : V (f selected)=if lay then 1 else 0) (one : (1:Word w)≠0)
    (bounds : S.pieceRadix<2^w ∧ 4<2^w ∧ S.degree<2^w ∧ 2^S.colors<2^w ∧ 2^t<2^w)
    (keyFits : ∀u,edgeId S P (baseNat b) bound u<2^w)
    (supplyFits : ∀u j,supply u j<2^w)
    (start kb : ℕ) (originWord : V (f nextWidths)=(start:Word w)) (keysAt : V (f keys)=(kb:Word w))
    (rem : V (f remaining)=((2^l:ℕ):Word w)) (remFits : 2^l<2^w)
    (supplyRows : ∀ a j, m (V (f issued)+
      (((denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val:Word w)*8+(j.val:Word w))).val =
        (supply a j:Word w))
    (p : (B × BitWord t) × Fin (liveDegree S+pad)) (y : BitWord l)
    (keyCap : kb+SlotImage.ordinal tagged p<2^w)
    (cap : start+SlotImage.edgeOrdinal tagged (tagOrdinal l) (p,y)<2^w)
    (here : vs 0=((start+SlotImage.edgeOrdinal tagged (tagOrdinal l) (p,y):ℕ):Word w))
    (keyWord : m (kb+SlotImage.ordinal tagged p)=(sourceKey S P b bound lay hc p:Word w)) :
    V (output S)=(SlotRefinement.actualWidth
      (fun e => S.pieces (typeIndex P binary_neg good lay e))
      (fun e : CrossEdge P lay => supply e.1 e.2)
      (allPieceSlots P binary_neg good lay S.pieces
        (edgeOrder P (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc pad)
      (p,y) : Word w) := by
  rw [output_chosen cell m vs S lay chosen one]
  let idx := Formula.cut (.reg 0) (f nextWidths)
  have which := PostImage.readKey (fun _=>cell) m vs tagged p y idx (f remaining) (f keys) kb _
    (cut_index cell m vs _ _ _ cap originWord here) rem keysAt (by omega) remFits keyCap keyWord
  obtain ⟨x,hx⟩ := (CompressorRefresh.slotCases (B × BitWord t) (liveDegree S) pad).symm.surjective p
  cases x with
  | inl u =>
    change CompressorRefresh.leftRow u=p at hx
    subst p
    let e := (ordinalOf S P (baseNat b) bound lay false hc).symm u
    have key := which.1
    rw [sourceKey_left] at key
    have out := ShrinkWidth.retained_value R W S.pieces S.pieceRadix S.liveDegree S.outputDegree bound
      hc lay e y (f keys) (f issued) (f remaining) idx (keyFits e) bounds key which.2
      supply supplyRows (supplyFits _ _)
    have correct := actualWidth_retained S P (baseNat b) bound hc lay good supply pad u y
    exact out.trans (congrArg (fun a:ℕ=>(a:Word w)) correct).symm
  | inr u =>
    change CompressorRefresh.rightRow u=p at hx
    subst p
    have key := which.1
    rw [sourceKey_right,Nat.cast_zero] at key
    have out := ShrinkWidth.padding_value (g:=g) (table:=f oldWidths) (tags:=f tags) (lanes:=f oldLanes)
      (d:=S.degree) (c:=S.colors) S.pieces S.pieceRadix S.liveDegree S.outputDegree lay (f keys) (f issued)
      (f remaining) idx key
    have correct := actualWidth_padding S P (baseNat b) bound hc lay good supply pad (u,y)
    rw [CompressorRefresh.unionLabels_right] at correct
    refine out.trans ?_
    simpa only [Nat.cast_zero, CompressorRefresh.rightRow] using
      (congrArg (fun a : ℕ => (a : Word w)) correct).symm


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
