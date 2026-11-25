import OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor
import OAI.ThreeFlat.Diagonal.CompressorSuccessorFiles
import OAI.ThreeFlat.Diagonal.ShrinkRowScan

namespace OAI
/-! # The branch-specific image of the actual binary shrinking stage -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Graph
open NavigationPass PhysicalShrink
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

private theorem base_chart {B L : Type} {d n n' lanes : ℕ} (G : LiftedSlots B d L) (base : B≃Fin n)
    (base' : B≃Fin n') (lane : L≃Fin lanes) (C : SlotImage.Columns) (mem : ℕ→ℕ) (width : SlotImage.Edge B L d→ℕ)
    (same : ∀ b,(base' b).val=(base b).val) (stored : SlotImage.Stored G base lane C mem width) :
    SlotImage.Stored G base' lane C mem width := by
  have card : n'=n := by simpa using Fintype.card_congr (base'.symm.trans base)
  refine ⟨by rw [card];exact stored.rowCount,?_,?_⟩
  · intro v rev j
    have eqv : SlotImage.cell C base' v rev j=SlotImage.cell C base v rev j := by simp only [SlotImage.cell,SlotImage.ordinal,same]
    rw [eqv,stored.graph]
    fin_cases j
    · exact (same _).symm
    · rfl
    · rfl
  · intro e
    simpa only [SlotImage.edgeOrdinal,SlotImage.ordinal,same] using stored.widthWord e

private theorem stored_raw {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H]
    {t l pad : ℕ} (S : Native.Graph.Stage)
    (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors) (b : B ≃ Fin (Fintype.card B))
    (bound : ∀ i, S.pieces i ≤ S.pieceRadix) (hc : 2 ≤ S.colors)
    (good : TagConditions P.slots (shift P) P.offset) (tag : 0 < t) (tagSize : 1 < 2^t)
    (lay : Bool) (supply raw : P.Motif → Fin 8 → ℕ) (sameSupply : supply = raw)
    (sameLayout : lay = ShrinkMotif.chooseWidths raw) (order : ShrinkEdge P S.pieces ↪ ℕ)
    (sameOrder : order = edgeOrder P (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound)
    (C : SlotImage.Columns) (mem : ℕ → ℕ)
    (image : SlotImage.Stored (successor (pad:=pad) S P b bound lay hc good tag)
      (productOrder b (tagOrdinal t)) (tagOrdinal l) C mem
      (newWidth (pad:=pad) S P b bound lay hc good supply)) :
    let chosen := ShrinkMotif.chooseWidths raw
    let use := shrinkingGraph P chosen S.pieces order hc binary_neg good
    let idle := tagPadding (V:=B) (L:=BitWord l) (adjacentMask tagSize) (adjacent_ne tagSize) pad
    let width := SlotRefinement.actualWidth (fun e => S.pieces (typeIndex P binary_neg good chosen e))
      (fun e : CrossEdge P chosen => raw e.1 e.2) (allPieceSlots P binary_neg good chosen S.pieces order hc pad)
    SlotImage.Stored (CompressorRefresh.union use idle) (productOrder b (tagOrdinal t)) (tagOrdinal l) C mem width := by
  subst supply
  subst lay
  subst order
  exact image

private theorem raw_at {lanes h t rem : ℕ} (T : ShrinkMotif.Table F) (s D : ℕ)
    (A : State (2^s) lanes)
    (u : BitWord lanes ≃+ BitWord (2*(2^s)+1) × BitWord h × BitWord t × BitWord rem)
    (P : PackingData A.Base (BitWord h) (BitWord t) (BitWord rem) (2^s) (2*(2^s)+1))
    (good : TagConditions P.slots (shift P) P.offset)
    (bound : ∀ i, (shrinkStage s D).pieces i ≤ (shrinkStage s D).pieceRadix)
    (hc : 2 ≤ 2*(2^s)+1) (tag : 0 < t) (tagSize : 1 < 2^t)
    (code : Arc A.Base (BitWord h) (BitWord t) (BitWord rem) (2^s) (2*(2^s)+1) ↪ ℕ)
    (order : ShrinkEdge P (shrinkStage s D).pieces ↪ ℕ)
    (sameOrder : order = edgeOrder P (baseNat A.order) (tagOrdinal t).toEmbedding
      (shrinkStage s D).pieces (shrinkStage s D).pieceRadix bound)
    (C : SlotImage.Columns) (mem : ℕ → ℕ) (id : ℕ) (len : P.Motif → Fin 8 → ℕ)
    (selected : ∀ j : Fin (Fintype.card (shrinkBranches T A u P (Nat.two_pow_pos s) code)), j.val=id →
      len = issued T P (oldWidth A u) code hc
        ((Fintype.equivFin (shrinkBranches T A u P (Nat.two_pow_pos s) code)).symm j))
    (image : SlotImage.Stored
      (successor (pad:=padding (2*(2^s)+1) (2^s) D) (shrinkStage s D) P A.order bound
        (ShrinkMotif.chooseWidths len) hc good tag)
      (productOrder A.order (tagOrdinal t)) (tagOrdinal rem) C mem
      (newWidth (pad:=padding (2*(2^s)+1) (2^s) D) (shrinkStage s D) P A.order bound
        (ShrinkMotif.chooseWidths len) hc good len)) :
    RawShrinkAt (D:=D) T A u P good (Nat.two_pow_pos s) tagSize code order C mem id := by
  intro j hj
  let raw := issued T P (oldWidth A u) code hc
    ((Fintype.equivFin (shrinkBranches T A u P (Nat.two_pow_pos s) code)).symm j)
  have eqv : len = raw := selected j hj
  exact stored_raw (pad:=padding (2*(2^s)+1) (2^s) D) (shrinkStage s D) P A.order bound hc good
    tag tagSize (ShrinkMotif.chooseWidths len) len raw eqv (congrArg ShrinkMotif.chooseWidths eqv)
    order sameOrder C mem image

variable (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
set_option quotPrecheck false
local notation "d" => (2^s:ℕ)
local notation "c" => (2*d+1:ℕ)
local notation "S" => shrinkStage s D
local notation "B" => shrinkRecordState s rem A
local notation "P" => shrinkRecordPacking s rem A
local notation "hc" => (show 2≤c from by have:=Nat.two_pow_pos s;omega)
open private tag_size rawConditions from OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor
local notation "good" => rawConditions s rem (shrinkRecordState s rem A)
local notation "M" => shrinkBinary T s D rem hD small A
local notation "stagePad" => PhysicalShrink.padding c d D
local notation "supply" => shrinkIssuedWords T s D rem hD small A

private theorem hist_at_value {α : Type} {one two : Fintype α}
    (i : Fin (@Fintype.card α one)) (j : Fin (@Fintype.card α two)) (h : i.val = j.val) :
    (@Fintype.equivFin α one).symm i = (@Fintype.equivFin α two).symm j := by
  cases Subsingleton.elim one two
  exact congrArg (@Fintype.equivFin α one).symm (Fin.ext h)

attribute [local irreducible] Finset.sum Finset.univ Fintype.card Fintype.equivFin
  shrinkingGraph SlotRefinement.actualWidth allPieceSlots

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem shrink_stored_at (branch : Fin (M).rules.count) (bound : ∀i,(S).pieces i≤(S).pieceRadix)
    (tag : 0<tagBits d) (C : SlotImage.Columns) (mem : ℕ→ℕ)
    (image : SlotImage.Stored
      (successor (pad:=stagePad) S P (B).order bound (ShrinkMotif.chooseWidths (supply branch)) hc good tag)
      (Template.tagNumber (t:=tagBits d) (B).order) (tagOrdinal rem) C mem
      (newWidth (pad:=stagePad) S P (B).order bound (ShrinkMotif.chooseWidths (supply branch)) hc good (supply branch))) :
    SlotImage.Stored ((M).next branch).graph ((M).next branch).order (tagOrdinal rem) C mem ((M).next branch).width := by
  have stored := base_chart
    (successor (pad:=stagePad) S P (B).order bound (ShrinkMotif.chooseWidths (supply branch)) hc good tag)
    (Template.tagNumber (t:=tagBits d) (B).order) (productOrder (B).order (tagOrdinal (tagBits d)))
    (tagOrdinal rem) C mem
    (newWidth (pad:=stagePad) S P (B).order bound (ShrinkMotif.chooseWidths (supply branch)) hc good (supply branch))
    (fun _=>rfl) image
  apply shrinkBinary_at T s D rem hD small A C mem branch.val _ branch rfl
  refine raw_at T s D B (shrinkRecordLane s rem) P good bound hc tag (tag_size s)
    (shrinkRecordCode s rem A) (shrinkRecordRoot s D rem A) rfl C mem branch.val
    (supply branch) ?_ stored
  intro j hj
  apply congrArg (issued T P (oldWidth B (shrinkRecordLane s rem)) (shrinkRecordCode s rem A) hc)
  exact hist_at_value (branch.cast (shrinkBinary_ruleCount T s D rem hD small A)) j hj.symm


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
