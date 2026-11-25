import OAI.ThreeFlat.Diagonal.CompressorUpperSource
import OAI.ThreeFlat.Diagonal.CompressorCDTest
import OAI.ThreeFlat.Diagonal.CompressorDemandPair

namespace OAI
/-! # Reading demand rows before finite histogram admission -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement
open scoped Classical Fin.NatCast
variable {n w c d t l N : ℕ} {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H]
variable {P : PackingData B H (BitWord t) (BitWord l) d c} {E : Codec B w c t l}
variable {data : Param → Word w} {m : Memory w} {vs : Fin n → Word w}
local notation "V" => Formula.value data m vs
variable {g : ArcColumns (F n)} (R : ArcReads P E (g.map (Formula.value data m vs)) m)
variable {table tags lanes residual : F n} {b : B ≃ Fin N}
variable {widths : Arc B H (BitWord t) (BitWord l) d c → ℕ}
variable (W : Demand.WidthReads P E (baseNat b) data m vs table tags lanes widths)
local notation "L" => Demand.layout table tags lanes d c

include R W
omit [Fintype B] [Fintype H] in
theorem decode_input (hc : 2≤c) (a : P.Motif) (row : F n) (bitsFit : 2^c<2^w)
    (dims : d<2^w ∧ 2^t<2^w ∧ 2^l<2^w) (hr : V residual=((2^l:ℕ):Word w))
    (fit : (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val<2^w)
    (hv : V row=((denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val : Word w)) :
    let z := decodeRow g L residual row
    z.1.map V=posCode P E (sourcePosition a.val) ∧ V z.2=(a.val.1.2.val:Word w) := by
  let size := 3*2^(c-2)
  let block := (a.val.1,a.val.2.2)
  let hi := (upperNumber P b (tagOrdinal t) (tagOrdinal l) block).val
  let word := tagOrdinal c a.val.2.1
  let low := blockIndex P a.val.1 a.val.2.2 word
  let rd := (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val
  have decomposition : rd=hi*size+low := denseMotifRow_value P b (tagOrdinal t) (tagOrdinal l) hc a
  have lowFit : low<size := by
    have h := blockIndex_listed P a.val.1 a.val.2.2 ((blockCoordinates P a).2) hc
    change blockIndex P a.val.1 a.val.2.2 ((blockCoordinates P a).2.val) < size
    rw [h]
    exact Fin.isLt _
  have hpos : 0<size := (Nat.zero_le low).trans_lt lowFit
  have qfit : size<2^w := by
    have hs : 2^c=2^(c-2)*4 := by
      conv_lhs => rw [show c=c-2+2 by omega,Nat.pow_add]
    dsimp [size]; omega
  have hhi : hi<2^w := (Nat.le_mul_of_pos_right hi hpos).trans_lt (by omega)
  have div : rd/size=hi := by rw [decomposition,Nat.mul_comm hi size,Nat.mul_add_div hpos,Nat.div_eq_of_lt lowFit,Nat.add_zero]
  have rem : rd%size=low := by simp [decomposition,Nat.add_mod,Nat.mod_eq_of_lt lowFit]
  let cut := Formula.op .div row (.lit size)
  let rank := Formula.op .mod row (.lit size)
  have hcutt : V cut=(hi:Word w) := by
    change BinaryOp.div.eval (V row) (size:Word w)=(hi:Word w)
    rw [hv,op_cast (w:=w) .div _ _ ⟨fit,qfit⟩]
    exact congrArg Nat.cast div
  have hrank : V rank=(low:Word w) := by
    change BinaryOp.mod.eval (V row) (size:Word w)=(low:Word w)
    rw [hv,op_cast (w:=w) .mod _ _ ⟨fit,qfit⟩]
    exact congrArg Nat.cast rem
  let xt := upperSource L residual cut
  obtain ⟨hx,hs⟩ := upper_code P b E table tags lanes residual cut block W.baseWord W.tags hr hcutt hhi dims
  have hsite : xt.1.site.map V = siteCode E a.val.1.1 := congrArg Placement.Position.site hx
  have hslot : V xt.1.slot=slotCode P a.val.2.2 := congrArg Placement.Position.slot hx
  have ht := test_code (table:=table) (tags:=tags) (lanes:=lanes) R hc bitsFit a xt.1 xt.2 rank hsite hslot hs hrank
  have hw := first_word (k:=2^c) (data:=data) (m:=m) (vs:=vs) (cdTest g L xt.1 xt.2 rank)
    word (List.finRange (2^c)) (List.mem_finRange word) ht
  have seen := hw.trans (Demand.tag_cast E.colors a.val.2.1)
  change ({xt.1 with bits := _} : Placement.Position (F n)).map V = _ ∧ V xt.2=_
  refine ⟨?_,hs⟩
  change Placement.Position.mk (xt.1.site.map V)
    (V (firstWord (b:=2^c) (cdTest g L xt.1 xt.2 rank) (List.finRange (2^c)))) (V xt.1.slot) =
    Placement.Position.mk (siteCode E a.val.1.1) (tagWord E.colors a.val.2.1) (slotCode P a.val.2.2)
  rw [hsite]
  exact congrArg₂ (Placement.Position.mk (siteCode E a.val.1.1)) seen hslot

/-- The two source-major demand words are exactly the AB and CD input amounts
used by the contracting algebraic layer. -/
theorem input_value (hc : 2≤c) (a : P.Motif) (index : F n) (j : Fin 2)
    (bitsFit : 2^c<2^w) (dims : d<2^w ∧ 2^t<2^w ∧ 2^l<2^w)
    (hr : V residual=((2^l:ℕ):Word w))
    (fit : 2*(denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val+j.val<2^w)
    (hv : V index=((2*(denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val+j.val:ℕ):Word w))
    (qFits : 3*(2^c*d)/4<2^w)
    (sumFits : CompressorPacking.thickWidth P widths (P.bundle a)<2^w) :
    V (inputPair g L residual index) =
      (demandWidth P widths (motifNumbers P (Demand.key P (baseNat b)) hc) a j : Word w) := by
  let row := (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val
  have rowFit : row<2^w := by change 2*row+j.val<2^w at fit; omega
  have twoFits : 2<2^w := by
    have lower : 2^2 ≤ 2^c := Nat.pow_le_pow_right (by decide : 0<2) hc
    omega
  let ix := Formula.op .div index (.lit 2)
  have divide : V ix=(row:Word w) := by
    change BinaryOp.div.eval (V index) (2:Word w)=(row:Word w)
    rw [hv]
    refine (op_cast (w:=w) .div (2*row+j.val) 2 ⟨fit,twoFits⟩).trans ?_
    exact congrArg (fun v : ℕ => (v : Word w)) (by
      change (2*row+j.val)/2=row
      rw [Nat.mul_add_div (by decide : 0<2),Nat.div_eq_of_lt j.isLt,Nat.add_zero])
  have rem : BinaryOp.mod.eval (V index) (2:Word w)=(j.val:Word w) := by
    rw [hv]
    refine (op_cast (w:=w) .mod (2*row+j.val) 2 ⟨fit,twoFits⟩).trans ?_
    exact congrArg (fun v : ℕ => (v : Word w)) (by
      change (2*row+j.val)%2=j.val
      rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt j.isLt])
  let z := decodeRow g L residual ix
  have hz := decode_input R W hc a ix bitsFit dims hr rowFit divide
  let e := ends (Demand.formulaOps n) g d false z.1 z.2
  have he : e.map V=encodeEnds P E a.val :=
    Demand.ends_code g R false z.1 z.2 (sourcePosition a.val) a.val.1.2 hz.1 hz.2
  have result := Demand.pair_value R W hc a e he qFits sumFits j
  have wordPos : w ≠ 0 := by
    rintro rfl
    norm_num at twoFits
  fin_cases j <;> simp [inputPair,Demand.fromSource,Formula.value,Comparison.test,rem,Fin.ofNat_eq_cast,wordPos] <;> exact result


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
