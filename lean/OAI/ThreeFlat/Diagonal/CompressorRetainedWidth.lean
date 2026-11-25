import OAI.ThreeFlat.Diagonal.CompressorDecodeWord
import OAI.ThreeFlat.Diagonal.CompressorWidthTranslation
import OAI.ThreeFlat.Diagonal.CompressorDenseRead
import OAI.ThreeFlat.Diagonal.CompressorDemandPair

namespace OAI
/-! # The retained physical width of each selected shrinking edge -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.CommRing
variable {n w c d t l N : ℕ} {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H]
variable {P : PackingData B H (BitWord t) (BitWord l) d c} {E : Codec B w c t l}
variable {data : Param → Word w} {mem : Memory w} {vs : Fin n → Word w}
variable {g : ArcColumns (F n)} (R : ArcReads P E (g.map (Formula.value data mem vs)) mem)
variable {table tags lanes : F n} {b : B ≃ Fin N}
variable {widths : Arc B H (BitWord t) (BitWord l) d c → ℕ}
variable (W : Demand.WidthReads P E (baseNat b) data mem vs table tags lanes widths)
variable (count : Fin 4 → ℕ) (radix live full : ℕ) (bound : ∀ k, count k≤radix)

def sourceMotif (layout : Bool) (e : ShrinkEdge P count) (y : BitWord l) : P.Motif :=
  moveMotif P (y-(siteOf P layout (supplyRoles layout e.1).1 e.2.1.val).2.2) e.2.1.val

private theorem selectZero (key yes no : F n) :
    Formula.value data mem vs (.select .eq key (.lit 0) yes no) =
      if Formula.value data mem vs key = 0 then Formula.value data mem vs yes
      else Formula.value data mem vs no := by
  simp [Formula.value, RAM.DescriptorExpr.Comparison.test]

/-- Padding width is read without interpreting any key digits or histogram. -/
theorem padding_value (layout : Bool) (keys issued rem i : F n)
    (empty : (Formula.value data mem vs) (.load (.op .add keys (.op .div i rem)))=0) :
    (Formula.value data mem vs) (output g (Demand.layout table tags lanes d c) (Graph.Stage.mk d c count radix live full) layout keys issued rem i)=0 := by
  unfold output
  rw [selectZero, ite_eq_left empty]; rfl

include R W
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1200000 in
omit [Fintype B] [Fintype H] in
theorem retained_value (hc : 2≤c) (layout : Bool) (e : ShrinkEdge P count) (y : BitWord l)
    (keys issued rem i : F n)
    (keyFits : 1+edgeKey P (baseNat b) (tagOrdinal t).toEmbedding count radix bound e<2^w)
    (dims : radix<2^w ∧ 4<2^w ∧ d<2^w ∧ 2^c<2^w ∧ 2^t<2^w)
    (keyRead : (Formula.value data mem vs) (.load (.op .add keys (.op .div i rem)))=
      ((1+edgeKey P (baseNat b) (tagOrdinal t).toEmbedding count radix bound e:ℕ):Word w))
    (laneRead : (Formula.value data mem vs) (.op .mod i rem)=tagWord E.lanes y)
    (supply : P.Motif → Fin 8 → ℕ)
    (read : ∀ a j, mem ((Formula.value data mem vs) issued+(((denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val:Word w)*8+
        (j.val:Word w))).val = (supply a j:Word w))
    (hwidth : supply (sourceMotif count layout e y) (ShrinkMotif.survivor layout e.1)<2^w) :
    (Formula.value data mem vs) (output g (Demand.layout table tags lanes d c) (Graph.Stage.mk d c count radix live full) layout keys issued rem i)=
      (SlotEnergy.piece (supply (sourceMotif count layout e y) (ShrinkMotif.survivor layout e.1)) (count e.1) e.2.2 : Word w) := by
  let key := Formula.load (.op .add keys (.op .div i rem))
  let lane := Formula.op .mod i rem
  let a := decode (Graph.Stage.mk d c count radix live full) tags key
  let x := unroot g (Graph.Stage.mk d c count radix live full) layout a lane
  let z := sourceMotif count layout e y
  let j := ShrinkMotif.survivor layout e.1
  let row := motifRow g (Demand.layout table tags lanes d c) x a.oldPort
  let edge := choose4 a.survivor (fun h => .lit (ShrinkMotif.survivor layout h).val)
  let loadWidth := Formula.load (.op .add issued (.op .add (.op .mul row (.lit 8)) edge))
  obtain ⟨old,port,kind,copy⟩ := decode_word P E (baseNat b) W.baseWord count radix live full bound tags key e
    W.tags keyRead keyFits dims
  have source : x.map (Formula.value data mem vs) = posCode P E (sourcePosition z.val) :=
    translate_code R count radix live full layout e.1 e.2.1 a lane y dims.2.1.le old port kind laneRead
  have physical : (Formula.value data mem vs) row=((denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc z).val:Word w) :=
    motifRow_code R W hc dims.2.2.2.1 x a.oldPort z source port
  have offset : (Formula.value data mem vs) edge=(j.val:Word w)  :=
    choose4_word data mem vs a.survivor (fun h => .lit (ShrinkMotif.survivor layout h).val) e.1 kind dims.2.1.le
  have actual : (Formula.value data mem vs) loadWidth=(supply z j:Word w) := by
    change mem ((Formula.value data mem vs) issued+((Formula.value data mem vs) row*8+(Formula.value data mem vs) edge)).val = _
    rw [physical,offset,read]
  have nonzero : (Formula.value data mem vs) key≠0 := by
    rw [keyRead]
    intro eq
    have z := congrArg Fin.val eq
    rw [Fin.val_cast_of_lt keyFits,Fin.val_zero] at z
    omega
  change (Formula.value data mem vs) (.select .eq key (.lit 0) (.lit 0) (choose4 a.survivor
    (fun h => Demand.balanced loadWidth (count h) a.copy))) = _
  rw [selectZero, ite_eq_right nonzero, choose4_word data mem vs a.survivor
    (fun h => Demand.balanced loadWidth (count h) a.copy) e.1 kind dims.2.1.le]
  exact Demand.balanced_value _ _ _ _ _ hwidth ((bound e.1).trans_lt dims.1) e.2.2.isLt actual copy


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
