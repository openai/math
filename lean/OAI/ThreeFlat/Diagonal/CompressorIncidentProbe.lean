import OAI.ThreeFlat.Diagonal.CompressorIncidentGeometry
import OAI.ThreeFlat.Diagonal.CompressorDenseRead
import OAI.ThreeFlat.Diagonal.CompressorWidthTranslation

namespace OAI
/-! # Physical fields and the election key for each valid local motif -/

noncomputable section

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Fin.CommRing Classical

variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w t l N : ℕ}
variable {S : Graph.Stage} (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l) (b : B ≃ Fin N)
variable (ptr : F) (data : Param → Word w) (mem : Memory w) (vs : Fin 1 → Word w)


def descriptor (hc : 2≤S.colors) (K : ℕ) (lay : Bool) (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
    (z : P.Motif) : Fin 6 → Word w :=
  let i := (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc z).val
  let ch := (Formula.value data mem vs) ((atField (Demand.formulaOps 1) ptr) choiceTable) + (i:Word w)*3
  ![((Demand.key P (baseNat b)) z.val:Word w),(Formula.value data mem vs) ((atField (Demand.formulaOps 1) ptr) countTable)+(i:Word w)*(K:Word w),mem (ch+1).val,mem ch.val,
    (pattern (edgeBits P lay s z):Word w),(pattern (partyBits P lay s z):Word w)]

variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
variable (R : ArcReads P E (((oldColumns (Demand.formulaOps 1) ptr)).map (Formula.value data mem vs)) mem)
variable (W : Demand.WidthReads P E (baseNat b) data mem vs ((atField (Demand.formulaOps 1) ptr) oldWidths) ((atField (Demand.formulaOps 1) ptr) tags) ((atField (Demand.formulaOps 1) ptr) oldLanes) prior)
variable (hi : Function.Injective E.base) (hc : 2≤S.colors) (bits : 2^S.colors<2^w) (masks : 8≤w)
variable (K : ℕ) (lay : Bool) (v : Placement.Site F) (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
variable (hv : v.map (Formula.value data mem vs)=siteCode E s) (a : Local.Slots S.degree S.colors)

set_option maxHeartbeats 1000000 in
include R W hi bits masks hv in
omit [Fintype B] [Fintype H] in
theorem visit_valid (z : P.Motif) (arc : (Local.incidentArc P a.1 s a.2)=z.val) :
    ((Formula.value data mem vs) ((visit ptr S K lay v a)).key=if (∃ j,partySite P lay z j=s) then (((Demand.key P (baseNat b)) z.val+1:ℕ):Word w) else 0) ∧
    (∀ j,(Formula.value data mem vs) (((visit ptr S K lay v a)).fields j)=descriptor P b ptr data mem vs hc K lay s z j) := by
  have one : (1:Word w)≠0 := by
    have : 1<2^w := by exact lt_of_lt_of_le (by decide : 1<2^8) (Nat.pow_le_pow_right (by decide) masks)
    intro h
    have eq : (1:Word w).val=0 := congrArg Fin.val h
    exact Nat.one_ne_zero ((show (1:Word w).val=1 from Fin.val_cast_of_lt ‹1<2^w›).symm.trans eq)
  let physical := probe (S:=S) ptr v a
  have ends : physical.map (Formula.value data mem vs) = encodeEnds P E z.val :=
    (probe_arc P E ptr data mem vs R v s hv a).trans (congrArg (encodeEnds P E) arc)
  have src : physical.source.map (Formula.value data mem vs)=posCode P E (sourcePosition z.val) := congrArg Ends.source ends
  have port : (Formula.value data mem vs) physical.originalSlot=(z.val.1.2.val:Word w) := congrArg Ends.originalSlot ends
  let idx := Demand.physical (widthLayout ptr S) physical.source physical.originalSlot
  let row := ShrinkWidth.motifRow (oldColumns (Demand.formulaOps 1) ptr) (widthLayout ptr S) physical.source physical.originalSlot
  have idxV : (Formula.value data mem vs) idx=((Demand.key P (baseNat b)) z.val:Word w) := Demand.address_code W z.val _ _ src port
  have rowV : (Formula.value data mem vs) row=((denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc z).val:Word w) :=
    ShrinkWidth.motifRow_code R W hc bits _ _ z src port
  have valid : (Formula.value data mem vs) (probeRoles (S:=S) ptr lay v a).valid=1 :=
    congrArg RoleSites.valid (probe_roles P E ptr data mem vs R v s hv a lay z arc)
  have read (j : Fin 6) := present_value P E ptr data mem vs R hi v s hv a lay z arc j
  have part : (Formula.value data mem vs) (mask (present (S:=S) ptr lay v a))=(pattern (partyBits P lay s z):Word w) := by
    apply mask_value
    intro j
    rw [read]
    cases partyBits P lay s z j <;> simp [one.symm]
  let localEdges := fun j : Fin 8 => Formula.select .eq ((present (S:=S) ptr lay v a) (ShrinkMotif.supplySrc j)) (.lit 1)
      ((present (S:=S) ptr lay v a) (ShrinkMotif.supplyDst j)) (.lit 0)
  have edges : (Formula.value data mem vs) (mask localEdges)=(pattern (edgeBits P lay s z):Word w) := by
    apply mask_value
    intro j
    simp only [localEdges,edgeBits,Formula.value,RAM.DescriptorExpr.Comparison.test,read,Fin.ofNat_eq_cast]
    cases partyBits P lay s z (ShrinkMotif.supplySrc j) <;>
      cases partyBits P lay s z (ShrinkMotif.supplyDst j) <;> simp [one.symm]
  have fit : pattern (partyBits P lay s z)<2^w :=
    (pattern_lt _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have zero : (Formula.value data mem vs) (mask (present (S:=S) ptr lay v a))=0 ↔ ¬∃ j,partySite P lay z j=s := by
    rw [part,Fin.ext_iff,Fin.val_cast_of_lt fit,Fin.val_zero,pattern_zero_iff]
    simp [partyBits]
  constructor
  · change (Formula.value data mem vs) (Formula.select .eq (probeRoles (S:=S) ptr lay v a).valid (.lit 1)
        (.select .eq (mask (present (S:=S) ptr lay v a)) (.lit 0) (.lit 0) (.op .add idx (.lit 1))) (.lit 0))=_
    by_cases h : ∃ j,partySite P lay z j=s
    · have nz : (Formula.value data mem vs) (mask (present (S:=S) ptr lay v a)) ≠ 0 := by simp [zero,h]
      simp [Formula.value,RAM.DescriptorExpr.Comparison.test,valid,nz,h,idxV,Nat.cast_add,BinaryOp.eval]
    · have zz := zero.mpr h
      simp [Formula.value,RAM.DescriptorExpr.Comparison.test,valid,h,zz]
  · intro j
    let count := Formula.op .add ((atField (Demand.formulaOps 1) ptr) countTable) (.op .mul row (.lit K))
    let choice := Formula.op .add ((atField (Demand.formulaOps 1) ptr) choiceTable) (.op .mul row (.lit 3))
    change (Formula.value data mem vs) ((![idx,count,.load (.op .add choice (.lit 1)),.load choice,mask localEdges,mask (present (S:=S) ptr lay v a)] : Fin 6 → F) j) = _
    fin_cases j <;> simp [descriptor,idxV,rowV,edges,part,count,choice,Formula.value,BinaryOp.eval]

include R hv in
omit [Fintype B] [Fintype H] in
theorem visit_invalid (bad : P.thick (sourcePosition (Local.incidentArc P a.1 s a.2)) ∧ P.thick (sourcePosition (P.actual (Local.incidentArc P a.1 s a.2))))
    (one : (1:Word w)≠0) : (Formula.value data mem vs) ((visit ptr S K lay v a)).key=0 := by
  have physical := probe_arc P E ptr data mem vs R v s hv a
  have rr := ShrinkWidth.roles_formula data mem vs (oldColumns (Demand.formulaOps 1) ptr) S.degree lay (probe (S:=S) ptr v a)
  rw [physical] at rr
  have invalid : (Formula.value data mem vs) (probeRoles (S:=S) ptr lay v a).valid=0 := (congrArg RoleSites.valid rr).trans
    (Graph.invalid_role S P E _ mem R lay (Local.incidentArc P a.1 s a.2) bad.1 bad.2)
  change (Formula.value data mem vs) (Formula.select .eq (probeRoles (S:=S) ptr lay v a).valid (.lit 1) _ (.lit 0))=0
  change (Formula.value data mem vs) (probeRoles (S:=S) ptr lay v a).valid=0 at invalid
  simp [Formula.value,RAM.DescriptorExpr.Comparison.test,invalid,one.symm]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end

end OAI
