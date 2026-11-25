import OAI.ThreeFlat.Diagonal.CompressorDemandGather

namespace OAI
/-! # The demand words fed to the physical histogram are the old wire widths -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Demand
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement Computability.VPVNP.Compression
open scoped Fin.NatCast BigOperators Classical
variable {n w d c t l : ℕ} {B H : Type*} [AddCommGroup H] [Fintype H] [Fintype B]
variable {P : PackingData B H (BitWord t) (BitWord l) d c} {E : Codec B w c t l} {base : B ↪ ℕ}
variable {data : Param → Word w} {m : Memory w} {vs : Fin n → Word w}
local notation "V" => Formula.value data m vs
variable {table tagCount laneCount : Formula n} {widths : Arc B H (BitWord t) (BitWord l) d c → ℕ}
variable {g : ArcColumns (Formula n)} (R : ArcReads P E (g.map (Formula.value data m vs)) m)
variable (W : WidthReads P E base data m vs table tagCount laneCount widths)
local notation "L" => layout table tagCount laneCount d c

theorem balanced_value (z index : Formula n) (a Q i : ℕ) (ha : a<2^w) (hq : Q<2^w) (hi : i<Q)
    (hz : V z=(a:Word w)) (hv : V index=(i:Word w)) :
    V (balanced z Q index) = ((a/Q + if i<a%Q then 1 else 0 : ℕ) : Word w) := by
  have hdiv : BinaryOp.div.eval (a:Word w) (Q:Word w) = ((a/Q:ℕ):Word w) :=
    op_cast .div a Q ⟨ha,hq⟩
  have hmod : BinaryOp.mod.eval (a:Word w) (Q:Word w) = ((a%Q:ℕ):Word w) :=
    op_cast .mod a Q ⟨ha,hq⟩
  have small : a%Q < 2^w := (Nat.mod_le _ _).trans_lt ha
  have cmp : ((i:Word w) < ((a%Q:ℕ):Word w)) ↔ i<a%Q := by
    rw [Fin.lt_def,Fin.val_cast_of_lt (hi.trans hq),Fin.val_cast_of_lt small]
  change BinaryOp.div.eval (V z) (Q:Word w) +
      (if RAM.DescriptorExpr.Comparison.test .lt (V index) (BinaryOp.mod.eval (V z) (Q:Word w)) then 1 else 0) = _
  by_cases h : i<a%Q <;> simp [hz,hv,hdiv,hmod,RAM.DescriptorExpr.Comparison.test,cmp,h]

include R W in
set_option maxHeartbeats 2400000 in
theorem pair_value (hc : 2 ≤ c) (motif : P.Motif) (e : Ends (Formula n))
    (enc : e.map (Formula.value data m vs) = encodeEnds P E motif.val)
    (qFits : 3*(2^c*d)/4 < 2^w) (totalFits : CompressorPacking.thickWidth P widths (P.bundle motif) < 2^w)
    (i : Fin 2) :
    (Formula.value data m vs) (pair g (layout table tagCount laneCount d c) (3*(2^c*d)/4) e i) =
      (demandWidth P widths (motifNumbers P (key P base) hc) motif i : Word w) := by
  let o := formulaOps n
  let mark := thickBit o g.toColumns e.source
  let chosen := Position.select o mark e.target e.source
  let s := toggle o g.toColumns chosen.site
  let k := physical (layout table tagCount laneCount d c) e.source e.originalSlot
  have hsource : e.source.map (Formula.value data m vs) = posCode P E (sourcePosition motif.val) := congrArg Ends.source enc
  have htarget : e.target.map (Formula.value data m vs) = posCode P E (sourcePosition (P.actual motif.val)) := congrArg Ends.target enc
  have hslot : (Formula.value data m vs) e.originalSlot=(motif.val.1.2.val : Word w) := congrArg Ends.originalSlot enc
  have hb : (Formula.value data m vs) mark=1 ↔ P.thick (sourcePosition motif.val) := bit_code g R _ _ hsource
  have pick : chosen.map (Formula.value data m vs) = posCode P E (P.C motif) := by
    apply (eval_select data m vs mark e.target e.source).trans
    by_cases hf : P.thick (sourcePosition motif.val)
    · rw [ite_eq_left (hb.mpr hf)]
      simpa only [PackingData.C,ite_eq_left hf] using htarget
    · rw [ite_eq_right (fun h=>hf (hb.mp h))]
      simpa only [PackingData.C,ite_eq_right hf] using hsource
  have site : s.map (Formula.value data m vs) = siteCode E (P.bundle motif).1 := by
    rw [show s.map (Formula.value data m vs) = _ from eval_toggle data m vs g chosen.site,show chosen.site.map (Formula.value data m vs) = _ from congrArg Placement.Position.site pick]
    exact toggle_site R.toGraphReads _
  have port : (Formula.value data m vs) chosen.slot=((P.bundle motif).2.val:Word w) := congrArg Placement.Position.slot pick
  have hkey : (Formula.value data m vs) k = (key P base motif.val : Word w) := address_code W _ _ _ hsource hslot
  fin_cases i
  · exact balanced_value _ _ _ _ _ totalFits qFits (motifNumbers P (key P base) hc motif).2.isLt
      (total_code R W (P.bundle motif) s chosen.slot site port)
      (rank_code R W hc motif s chosen.slot k site port hkey)
  · exact read_code W _ _ _ hsource hslot


end ThreeFlat.Diagonal.CompressorPacking.Native.Demand

end OAI
