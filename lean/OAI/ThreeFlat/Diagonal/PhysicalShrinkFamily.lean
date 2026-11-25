import OAI.ThreeFlat.Diagonal.PhysicalStageBinary
import OAI.ThreeFlat.Diagonal.CompressorDenseMotifs
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.PhysicalRecordAlphabet
import OAI.ThreeFlat.Diagonal.PhysicalShrinkCopies
import OAI.ThreeFlat.Diagonal.PhysicalStateWidth

namespace OAI
/-! # The branch register of the actual binary shrinking move

The term ordinal uses the same finite enumeration as the physical rewriting
rule. Rows in that register use the dense CD order of the width reader and
the original alphabet of the selected tile.
-/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.Compression CompressorPacking PhysicalShrink MotifOuterTerms
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]
private theorem count_degree {d l D D' rem : ℕ} {A : State d l}
    (e : D=D') (j : Move F A D rem) :
    (e ▸ j : Move F A D' rem).rules.count=j.rules.count := by cases e; rfl

private theorem count_input {d i j D rem : ℕ} (eqv : i=j) (A : State d i)
    (R : Move F (eqv ▸ A : State d j) D rem) :
    (Move.recastInputLanes eqv A R).rules.count=R.rules.count := by cases eqv; rfl

set_option maxRecDepth 8192 in
private theorem shrinkMove_count {d lanes rem h t D : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord h × BitWord t × BitWord rem)
    (P : PackingData A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset)
    (hd : 0<d) (hD : 0<D) (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D ≤ 1/1024)
    (tagSize : 1<2^t) (code : Arc A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) :
    (shrinkMove T A u P agree good hd hD small tagSize code order).rules.count =
      Fintype.card (shrinkBranches T A u P hd code) := by
  unfold shrinkMove
  apply count_degree

variable (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
  (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
  (A : State (2^s) (shrinkCharge s+rem))

private theorem lanes_eq : shrinkCharge s+rem=(2*(2^s)+1)+(s+(tagBits (2^s)+rem)) := by
  simp [shrinkCharge,Nat.add_assoc]

abbrev shrinkRecordState := (lanes_eq s rem ▸ A : State (2^s) ((2*(2^s)+1)+(s+(tagBits (2^s)+rem))))
private abbrev rawPacking (S : State (2^s) ((2*(2^s)+1)+(s+(tagBits (2^s)+rem)))) :=
  Ordered.binaryPacking S.order.symm S.graph
abbrev shrinkRecordPacking := rawPacking s rem (shrinkRecordState s rem A)
abbrev shrinkRecordLane := laneSplit (2*(2^s)+1) s (tagBits (2^s)) rem
abbrev shrinkRecordWidth := oldWidth (shrinkRecordState s rem A) (shrinkRecordLane s rem)
private abbrev rawCode (S : State (2^s) ((2*(2^s)+1)+(s+(tagBits (2^s)+rem)))) :=
  demandOrdinal (rawPacking s rem S) (baseNat S.order) (Native.tagOrdinal (tagBits (2^s))).toEmbedding
  (Native.tagOrdinal rem).toEmbedding
abbrev shrinkRecordCode := rawCode s rem (shrinkRecordState s rem A)
private theorem colors_le : 2≤2*(2^s)+1 := by have := Nat.two_pow_pos s; omega

abbrev shrinkRecordOrder := denseMotifRow (shrinkRecordPacking s rem A) (shrinkRecordState s rem A).order
  (Native.tagOrdinal (tagBits (2^s))) (Native.tagOrdinal rem) (colors_le s)
abbrev shrinkRecordTile := tile T (shrinkRecordPacking s rem A) (shrinkRecordWidth s rem A)
  (shrinkRecordCode s rem A) (colors_le s)
abbrev shrinkRecordCopies := r T (shrinkRecordPacking s rem A) (shrinkRecordWidth s rem A)
  (shrinkRecordCode s rem A) (colors_le s)
abbrev shrinkRecordHists := (m : (shrinkRecordPacking s rem A).Motif) →
  Histogram (shrinkRecordTile T s rem A m).Alphabet (shrinkRecordCopies T s rem A m)

private abbrev branchFintype {d lanes rem h t : ℕ} (T : ShrinkMotif.Table F) (S : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord h × BitWord t × BitWord rem)
    (P : PackingData S.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1))
    (hd : 0<d) (code : Arc S.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1) ↪ ℕ) :
    Fintype (shrinkBranches T S u P hd code) := inferInstance

local instance : Fintype (shrinkRecordHists T s rem A) :=
  branchFintype T (shrinkRecordState s rem A) (shrinkRecordLane s rem) (shrinkRecordPacking s rem A)
    (Nat.two_pow_pos s) (shrinkRecordCode s rem A)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem raw_ruleCount (S : State (2^s) ((2*(2^s)+1)+(s+(tagBits (2^s)+rem)))) :
    (shrinkRaw T s D rem hD small S).rules.count =
      Fintype.card (shrinkBranches T S (shrinkRecordLane s rem) (rawPacking s rem S)
        (Nat.two_pow_pos s) (rawCode s rem S)) := by
  let d := 2^s
  let P := rawPacking s rem S
  let n := parallel (2*d+1) d D
  let rooted := edgeOrder P (baseNat S.order) (Native.tagOrdinal (tagBits d)).toEmbedding n
    (∑ i : Fin 4,n i) (fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have tagSize : 1<2^(tagBits d) := by
    have enough := tagBits_fit d
    rw [show Fintype.card (BitWord (tagBits d)) = 2^(tagBits d) by simp [BitWord]] at enough
    have pos : 0<d := Nat.two_pow_pos _
    have lower : 1≤2*d*((d+1)+(d+1)^2) :=
      Nat.mul_pos (Nat.mul_pos (by decide) pos) (by omega)
    omega
  exact shrinkMove_count T S (shrinkRecordLane s rem) P rfl
    (Ordered.binaryPacking_conditions S.order.symm S.graph) (Nat.two_pow_pos s) hD small tagSize
    (rawCode s rem S) rooted

section
attribute [local irreducible] shrinkRaw Move.recastInputLanes Ordered.binaryPacking

/-- The count is independent of the finite enumeration used for the concrete register. -/
private theorem raw_ruleCount_for (S : State (2^s) ((2*(2^s)+1)+(s+(tagBits (2^s)+rem))))
    (fin : Fintype (shrinkBranches T S (shrinkRecordLane s rem) (rawPacking s rem S)
      (Nat.two_pow_pos s) (rawCode s rem S))) :
    (shrinkRaw T s D rem hD small S).rules.count = @Fintype.card _ fin := by
  exact (raw_ruleCount T s D rem hD small S).trans
    (congrArg (fun inst : Fintype _ => @Fintype.card _ inst) (Subsingleton.elim _ fin))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1400000 in
theorem shrinkBinary_ruleCount :
    (shrinkBinary T s D rem hD small A).rules.count=Fintype.card (shrinkRecordHists T s rem A) := by
  unfold shrinkBinary
  exact (count_input (lanes_eq s rem) A (shrinkRaw T s D rem hD small (shrinkRecordState s rem A))).trans
    (raw_ruleCount_for T s D rem hD small (shrinkRecordState s rem A)
      (show Fintype (shrinkRecordHists T s rem A) from inferInstance))

end

def shrinkBinaryFamily : RecordFamily (shrinkBinary T s D rem hD small A).rules.count where
  motifs := Fintype.card (shrinkRecordState s rem A).Base*2^s*2^rem*2^(tagBits (2^s))*2^s*
    (3*2^(2*(2^s)+1-2))
  alphabet i := (shrinkRecordTile T s rem A ((shrinkRecordOrder s rem A).symm i)).Alphabet
  finiteAlphabet _ := inferInstance
  copies i := shrinkRecordCopies T s rem A ((shrinkRecordOrder s rem A).symm i)
  order := (finCongr (shrinkBinary_ruleCount T s D rem hD small A)).trans
    ((Fintype.equivFin (shrinkRecordHists T s rem A)).symm.trans
      (Equiv.piCongrLeft' (fun m=>Histogram (shrinkRecordTile T s rem A m).Alphabet
        (shrinkRecordCopies T s rem A m)) (shrinkRecordOrder s rem A)))

local notation "Q" => shrinkBinaryFamily T s D rem hD small A

theorem shrinkBinaryFamily_motifs :
    (Q).motifs = Fintype.card A.Base*2^s*2^rem*2^(tagBits (2^s))*2^s*(3*2^(2*(2^s)+1-2)) := by
  have cast_base {d i j : ℕ} (eqv : i=j) (a : State d i) :
      Fintype.card (eqv ▸ a : State d j).Base=Fintype.card a.Base := by cases eqv; rfl
  change Fintype.card (shrinkRecordState s rem A).Base * _ * _ * _ * _ * _ = _
  rw [shrinkRecordState,cast_base]

theorem shrinkBinaryFamily_copies (m : (shrinkRecordPacking s rem A).Motif) :
    (Q).copies (shrinkRecordOrder s rem A m)=shrinkRecordCopies T s rem A m := by
  change shrinkRecordCopies T s rem A ((shrinkRecordOrder s rem A).symm (shrinkRecordOrder s rem A m))=_
  rw [Equiv.symm_apply_apply]

theorem shrinkBinaryFamily_order (j : Fin (shrinkBinary T s D rem hD small A).rules.count) (i : Fin (Q).motifs) :
    (Q).order j i = (Fintype.equivFin (shrinkRecordHists T s rem A)).symm
      (j.cast (shrinkBinary_ruleCount T s D rem hD small A)) ((shrinkRecordOrder s rem A).symm i) := rfl

theorem shrinkBinaryFamily_symbol (j : Fin (shrinkBinary T s D rem hD small A).rules.count)
    (i : Fin (Q).motifs) (b : Fin (Fintype.card ((Q).alphabet i))) :
    (((Q).order j i).val ((Fintype.equivFin ((Q).alphabet i)).symm b)).val =
      ((((Fintype.equivFin (shrinkRecordHists T s rem A)).symm
          (j.cast (shrinkBinary_ruleCount T s D rem hD small A))) ((shrinkRecordOrder s rem A).symm i)).val
        ((Fintype.equivFin ((Q).alphabet i)).symm b)).val := rfl

theorem shrinkBinaryFamily_fits {K W : ℕ} (k : shrinkSymbolBound T≤K)
    (bound : shrinkCopyFactor (2*(2^s)+1) (2^s)*(1+A.maxWidth)<2^W) : (Q).Fits K W := by
  constructor
  · intro i
    apply le_trans _ k
    apply Finset.le_sup (s:=Finset.univ) (f:=fun j=>Fintype.card (T.block j).Alphabet)
    exact Finset.mem_univ _
  · intro i
    apply lt_of_le_of_lt _ bound
    apply PhysicalShrink.copies_le
    intro e
    have cast_max {d i j : ℕ} (eqv : i=j) (a : State d i) :
        (eqv ▸ a : State d j).maxWidth=a.maxWidth := by cases eqv; rfl
    exact (shrinkRecordState s rem A).width_le_maxWidth _ |>.trans_eq (cast_max (lanes_eq s rem) A)

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
