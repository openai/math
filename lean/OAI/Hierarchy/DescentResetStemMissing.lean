import OAI.Hierarchy.DescentResetStemIncidence
import OAI.Hierarchy.DescentResetStemHalo

namespace OAI
/-! # Reading the receiver's old self-neighbor flag from its actual roster -/
namespace Hierarchy.DescentResetOriginHaloRAM
open DescentPackedColony DescentPackedZip DescentSortedRoster DescentPacking.SparseBinRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentFallbackRankRAM DescentResetStemIncidence
open private Hierarchy.DescentResetStemIncidence.target_eq
  Hierarchy.DescentResetStemIncidence.mask_fits
  Hierarchy.DescentResetStemIncidence.mask_work
  from OAI.Hierarchy.DescentResetStemIncidence
open scoped Classical Fin.CommRing
noncomputable section
variable {H D w : ℕ}

def missing (D : ℕ) (roster : Bank) : Expr:=unlessSeen .row (.lit 1) (List.ofFn (opened (D:=D) roster))

theorem missing_run (roster : Bank) (p : Fin H→Fin D→Option (Fin H)) (out : ℕ) (m : Memory w)
    (fit : roster.Fits w out) (extent : H*D≤roster.size)
    (stored : ∀v i,m (roster.base+(v.val*D+i.val))=(target (p v i):Word w))
    (high : H<2^w) (space : out+H<2^w) :
    let op:=missing D roster
    let dst:=image out H op m
    (scan w out H op).Exec m dst (4+H*(2*op.work+4)) ∧ CheapCode (scan w out H op) ∧
      (∀v : Fin H,dst (out+v.val)=((decide (v∉present p v)).toNat:Word w)) ∧
      ∀x,x<out ∨ out+H≤x→dst x=m x := by
  intro op dst
  have opFit : op.Fits w out:=by
    apply Hierarchy.DescentResetStemIncidence.mask_fits _ _ (show (Expr.row).Fits w out from trivial)
    intro e he;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
    have small (n : ℕ) : (ProtocolRAM.scale n .row).Fits w out := by
      induction n with
      | zero => trivial
      | succ n ih => exact ⟨trivial, ih⟩
    exact ⟨fit,small D,trivial⟩
  refine ⟨scan_exec _ _ _ _ opFit space,@scan_cheap _ _ _ _,?_,fun x hit => ProtocolRAMGeneratedWrite.frame_image out H op m x hit⟩
  intro v
  change image out H op m (out+v.val) = _
  rw [ProtocolRAMGeneratedWrite.read_image out H op m v]
  change (unlessSeen .row (.lit 1) (List.ofFn (opened roster : Fin D→Expr))).eval m (v.val:Word w)=_
  rw [unlessSeen_eval]
  have one (i : Fin D) : (opened roster i).eval m (v.val:Word w)=(target (p v i):Word w):=by
    change roster.read m ((ProtocolRAM.scale D .row).eval m (v.val:Word w)+(i.val:Word w))=_
    rw [eval_scale]
    change roster.read m ((D:Word w)*(v.val:Word w)+(i.val:Word w))=_
    have below:v.val*D+i.val<H*D:=(Nat.add_lt_add_left i.isLt _).trans_le
      (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
    rw [mul_comm (D:Word w),←Nat.cast_mul,←Nat.cast_add,bank_read _ _ (below.trans_le extent) fit,stored]
  have iff_ : (∃e∈List.ofFn (opened roster : Fin D→Expr),e.eval m (v.val:Word w)=(v.val:Word w)) ↔ v∈present p v:=by
    simp only [present,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨_,h,eqn⟩;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp h
      exact ⟨i,(Hierarchy.DescentResetStemIncidence.target_eq _ _ high).1 ((one i).symm.trans eqn)⟩
    · rintro ⟨i,hi⟩
      exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,(one i).trans ((Hierarchy.DescentResetStemIncidence.target_eq _ _ high).2 hi)⟩
  simp only [Expr.eval,iff_]
  by_cases live:v∈present p v <;> simp [live]

theorem missing_work (D : ℕ) (roster : Bank) :
    (missing D roster).work≤1+D*(2*(1+D*(2+1)+1+1+5)+2) := by
  unfold missing
  have cap : ∀i:Fin D,(opened roster i).work=1+D*(2+1)+1+1+5:=by
    intro i
    change (ProtocolRAM.scale D .row).work+1+1+5=_
    rw [ProtocolRAM.scale_work];rfl
  simpa using Hierarchy.DescentResetStemIncidence.mask_work .row (List.ofFn (opened roster : Fin D→Expr))
    (U:=1+D*(2+1)+1+1+5) (by change 2≤_;omega)
    (by intro e he;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;exact (cap j).le)
end
end Hierarchy.DescentResetOriginHaloRAM

end OAI
