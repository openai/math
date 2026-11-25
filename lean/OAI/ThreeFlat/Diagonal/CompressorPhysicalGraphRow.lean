import OAI.ThreeFlat.Diagonal.CompressorRowCoordinates

namespace OAI
/-! # A complete successor graph cell, including the chosen orientation and padding branch -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement Graph
open scoped BigOperators Classical Fin.NatCast
variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l n : ℕ}
variable (cell : Word w) (pub : Fin 1 → Word w) (m : Memory w) (vs : Fin 1 → Word w)
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (E : Codec B w S.colors t l) (R : ArcReads P E ((oldColumns (Demand.formulaOps 1) ptr).map (Formula.value (fun _ => cell) m vs)) m)
variable (hb : ∀z,E.base z=((b z).val:Word w)) (hi : Function.Injective E.base)
variable (bound : ∀i,S.pieces i≤S.pieceRadix) (fit : ∀e,edgeId S P (baseNat b) bound e<2^w)
variable (lay : Bool) (hc : 2≤S.colors) (good : TagConditions P.slots (shift P) P.offset)
include pub R hb hi fit in
theorem physical_graph_read (ht : 0<t)
    (rad : (radices o ptr S).map (Formula.value (fun _ => cell) m vs) = rowRadices (w:=w) (t:=t) (l:=l) S)
    (liveEq : S.liveDegree=liveDegree S) (degreeEq : S.outputDegree=(liveDegree S+n))
    (chosen : (Formula.value (fun _ => cell) m vs) (f selected)=if lay then 1 else 0) (one : (1:Word w)≠0)
    (six : 6≤2^w) (degFit : (liveDegree S+n)<2^w) (tagsFit : 2^t<2^w)
    (basesFit : ∀v : B × BitWord t,(E.base v.1).val*2^t+(tagOrdinal t v.2).val<2^w)
    (C : SlotImage.Columns) (rows : C.rows=(N*2^t)*(liveDegree S+n)) (fits : C.graph+6*C.rows<2^w)
    (start : (Formula.value (fun _ => cell) m vs) (f nextGraph)=(C.graph:Word w)) (length : (Formula.value (fun _ => cell) m vs) (f nextSlots)=(C.rows:Word w))
    (p : (B × BitWord t) × Fin (liveDegree S+n)) (rev : Bool) (j : Fin 3)
    (here : vs 0=((SlotImage.cell C (tagNumber (t:=t) b) p rev j):Word w)) :
    let liveGraph := shrinkingGraph P lay S.pieces
      (edgeOrder P (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc binary_neg good
    let pad := tagPadding (V:=B) (L:=BitWord l) (tagOne ht) (tagOne_ne ht) n
    (Formula.value (fun _ => cell) m vs) (graph S false)=((SlotImage.fields (CompressorRefresh.union liveGraph pad) (tagNumber (t:=t) b)
      (tagOrdinal l) p rev j):Word w) := by
  dsimp only
  let tagged := tagNumber (t:=t) b
  let liveGraph := shrinkingGraph P lay S.pieces
    (edgeOrder P (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc binary_neg good
  let fld := SlotImage.column rev j
  let dest := column o (f nextGraph) (f nextSlots) fld
  let whereRow := SlotImage.ordinal tagged p
  have inCol : whereRow<C.rows := rows ▸ SlotImage.ordinal_lt tagged p
  have hf : fld<6 := (columnNumber rev j).isLt
  have hd : C.graph+C.rows*fld+whereRow < C.graph+6*C.rows := by
    have mul := Nat.mul_le_mul_left C.rows hf
    rw [Nat.mul_succ] at mul
    omega
  have term := columnNumber_read cell m vs S lay rev j C.graph C.rows whereRow six (by omega)
    inCol (hd.trans fits) start length here chosen one
  rw [term]
  have rowsFit : C.rows < 2^w := by omega
  have rowFit : (tagged p.1).val*(liveDegree S+n)+p.2.val < 2^w :=
    inCol.trans rowsFit
  have addr := split_address cell m vs dest (C.graph+C.rows*fld) (tagged p.1).val p.2.val S.outputDegree
    (by rw [degreeEq]; exact degFit) (by rw [degreeEq]; exact p.2.isLt)
    (by rw [degreeEq]; exact rowFit) (value_column cell m vs _ _ start length fld)
    (by rw [degreeEq]; exact here)
  have baseFit : (tagged p.1).val < 2^w :=
    (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt p.2.isLt)).trans_lt
      ((Nat.le_add_right _ p.2.val).trans_lt rowFit)
  have liveFits : liveDegree S<2^w := (Nat.le_add_right _ n).trans_lt degFit
  obtain ⟨x,hx⟩ := (CompressorRefresh.slotCases (B × BitWord t) (liveDegree S) n).symm.surjective p
  cases x with
  | inl u =>
    change CompressorRefresh.leftRow u=p at hx
    subst p
    let pad := tagPadding (V:=B) (L:=BitWord l) (tagOne ht) (tagOne_ne ht) n
    apply physical_live cell pub m vs S P b E R hb hi bound fit lay hc good one rad
      liveFits.le tagsFit basesFit rev u j dest _ _ _ pad
    · exact addr.1.trans (packed_word S b E hb u.1).symm
    · exact addr.2
    · rw [liveEq]
      change ((u.2.val:Word w).val < (liveDegree S:Word w).val)
      rw [Fin.val_cast_of_lt (u.2.isLt.trans liveFits),Fin.val_cast_of_lt liveFits]
      exact u.2.isLt
  | inr u =>
    change CompressorRefresh.rightRow u=p at hx
    subst p
    apply physical_pad cell m vs S b liveGraph ht (by omega) u baseFit lay rev j dest addr.1 addr.2
    rw [liveEq]
    have indexFit : liveDegree S+u.2.val<2^w := (Nat.add_lt_add_left u.2.isLt _).trans degFit
    change ¬ ((liveDegree S+u.2.val:ℕ):Word w).val < (liveDegree S:Word w).val
    rw [Fin.val_cast_of_lt indexFit,Fin.val_cast_of_lt liveFits]
    exact Nat.not_lt_of_ge (Nat.le_add_right _ _)


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
