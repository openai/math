import OAI.ThreeFlat.Diagonal.CompressorDenseMotifs
import OAI.ThreeFlat.Diagonal.CompressorDemandROM
import OAI.ThreeFlat.Diagonal.CompressorShrinkWidthWriter
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI
/-! # The width writer addresses the dense global histogram record -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Fin.CommRing BigOperators Classical
variable {B H : Type*} [AddCommGroup H] {n w d c t l N : ℕ}
variable {P : PackingData B H (BitWord t) (BitWord l) d c} {E : Codec B w c t l}
variable {data : Param → Word w} {m : Memory w} {vs : Fin n → Word w}
local notation "V" => Formula.value data m vs
variable {g : ArcColumns (F n)} (R : ArcReads P E (g.map (Formula.value data m vs)) m)
variable {table tags lanes : F n}
local notation "L" => Demand.layout table tags lanes d c

private theorem block_sum (p : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin d) (h : H)
    (v : Fin (2^c)) :
    blockIndex P p h v = ∑ u : Fin (2^c),
      if u<v ∧ u∈oldBlock P p h then 1 else 0 := by
  rw [Finset.sum_boole]
  apply congrArg Finset.card
  ext u
  simp [and_comm]

include R
theorem lowerCD_code (x : Placement.Position (F n)) (port : F n) (a : Arc B H (BitWord t) (BitWord l) d c)
    (hx : x.map V = posCode P E (sourcePosition a)) (hp : V port=(a.1.2.val:Word w)) :
    V (lowerCD g L x port) = (blockIndex P a.1 a.2.2 (tagOrdinal c a.2.1) : Word w) := by
  rw [lowerCD,Demand.totals_word,List.map_map,←Fin.sum_univ_def,block_sum,Nat.cast_sum]
  simp only [Demand.layout]
  apply Finset.sum_congr rfl
  intro u _
  let ux := {x with bits := Formula.lit u.val}
  let b : Arc B H (BitWord t) (BitWord l) d c := (a.1,(tagOrdinal c).symm u,a.2.2)
  let ue := ends (Demand.formulaOps n) g d false ux port
  have hux : ux.map V = posCode P E (sourcePosition b) := by
    have site := congrArg Placement.Position.site hx
    have label := congrArg Placement.Position.slot hx
    simp only [ux,Placement.Position.map,posCode,sourcePosition] at site label ⊢
    simp only [site,label,b,Formula.value,Fin.ofNat_eq_cast,←Demand.tag_cast,Equiv.apply_symm_apply]
  have he : ue.map V = encodeEnds P E b :=
    Demand.ends_code g R false ux port (sourcePosition b) a.1.2 hux hp
  have h1 := Demand.bit_code g R ux _ hux
  have h2 := Demand.bit_code g R ue.target _ (congrArg Ends.target he)
  have hbits : V x.bits=tagWord E.colors a.2.1 := congrArg Placement.Position.bits hx
  have cmp : (u.val : Word w) < V x.bits ↔ u < tagOrdinal c a.2.1 := by
    rw [hbits]
    change ((u.val : Word w).val < (tagOrdinal c a.2.1).val) ↔ u.val < (tagOrdinal c a.2.1).val
    rw [Fin.val_cast_of_lt (u.isLt.trans_le (Nat.pow_le_pow_right (by decide) E.colors))]
  change V (.select .lt (.lit u.val) x.bits ((Demand.formulaOps n).choose
    (thickBit (Demand.formulaOps n) g.toColumns ux) (.lit 1)
    ((Demand.formulaOps n).choose (thickBit (Demand.formulaOps n) g.toColumns ue.target) (.lit 1) (.lit 0) (.lit 1))
    (.lit 1)) (.lit 0)) = _
  have member : u ∈ oldBlock P a.1 a.2.2 ↔
      ¬(P.thick (sourcePosition b) ∧ P.thick (sourcePosition (P.actual b))) := by
    rw [oldBlock,Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ u)
  simp only [Demand.eval_lt,Demand.eval_choose]
  by_cases less : u < tagOrdinal c a.2.1 <;>
    by_cases src : P.thick (sourcePosition b) <;> by_cases dst : P.thick (sourcePosition (P.actual b)) <;>
    simp [Formula.value,Fin.ofNat_eq_cast,cmp,h1,h2,
      less,src,dst,member]

variable {b : B ≃ Fin N} {widths : Arc B H (BitWord t) (BitWord l) d c → ℕ}
variable (W : Demand.WidthReads P E (baseNat b) data m vs table tags lanes widths)
include W
theorem motifRow_code (hc : 2≤c) (bitsFit : 2^c<2^w) (x : Placement.Position (F n))
    (port : F n) (a : P.Motif) (hx : x.map V=posCode P E (sourcePosition a.val))
    (hp : V port=(a.val.1.2.val:Word w)) :
    V (motifRow g L x port) = ((denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val : Word w) := by
  have addr := Demand.address_code W a.val x port hx hp
  have div := op_cast (w:=w) .div (Demand.key P (baseNat b) a.val) (2^c) ⟨W.ordinalFits _,bitsFit⟩
  change (BinaryOp.div.eval (V (Demand.physical L x port)) ((2^c : ℕ) : Word w)) *
    ((3*2^(c-2) : ℕ) : Word w) + V (lowerCD g L x port) = _
  rw [addr,div,lowerCD_code R x port a.val hx hp,denseMotifRow_value,Nat.cast_add,Nat.cast_mul]
  rw [←upperNumber_physical]
  simp only [Nat.cast_mul,natOp,Demand.key]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
