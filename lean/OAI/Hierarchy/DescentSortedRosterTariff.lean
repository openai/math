import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentMountedSortedRoster

namespace OAI
/-! # Size of the scan that restores canonical neighbor order once per host -/
namespace Hierarchy.DescentSortedRoster
open DescentFallbackRankRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D H w : ℕ}

private theorem guard_work (C : Chart) (j : Fin D) (e : Expr) (xs : List (Fin D)) :
    (unlessSeen (get C j) e (xs.map (get C))).work=e.work+30*xs.length := by
  induction xs with
  | nil=>simp [unlessSeen]
  | cons i xs ih=>
    change 14+14+1+(unlessSeen (get C j) e (xs.map (get C))).work+1=_
    rw [ih,List.length_cons]
    omega

private theorem sum_work (xs : List Expr) (n : ℕ) (each : ∀a∈xs,a.work≤n) :
    (foldSum xs).work≤1+xs.length*(n+1) := by
  induction xs with
  | nil=>simp [foldSum,Expr.work]
  | cons x xs ih=>
    have first:=each x (by simp)
    have rest:=ih (fun a ha=>each a (List.mem_cons_of_mem _ ha))
    change x.work+(foldSum xs).work+1≤_
    rw [List.length_cons,Nat.succ_mul]
    omega

private theorem calc_work (C : Chart) (v : Fin D) :
    (calculate (get (D:=D) C) (get C v)).work≤1+D*(32+30*D) := by
  have rb (j : Fin D) : (rankBit (get C) (get C v) j).work≤31+30*D := by
    rw [rankBit,guard_work]
    have le : (prior j).length≤D := by
      simpa [prior,Finset.length_toList] using (Finset.card_filter_le (s:=Finset.univ) (fun i : Fin D=>i<j))
    change 31+30*(prior j).length≤_
    omega
  have h:=sum_work ((Finset.univ : Finset (Fin D)).toList.map (rankBit (get C) (get C v))) (31+30*D) (by
    intro e h
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp h
    exact rb j)
  simp only [List.length_map,Finset.length_toList,Finset.card_univ,Fintype.card_fin] at h
  simpa only [calculate,show 31+30*D+1=32+30*D by omega] using h

theorem code_work (C : Chart) (D H : ℕ) : (code C D H).work≤100*(D+1)^3 := by
  let bound:=44+D*(32+30*D)
  have one (xs : List (Fin D)) :
      (pick (get C) (.lookup C.slot .row) H xs).work≤1+xs.length*bound := by
    induction xs with
    | nil=>simp [pick,Expr.work]
    | cons i xs ih=>
      have b:=calc_work C i
      change (14+1+((calculate (get (D:=D) C) (get C i)).work+7+1+1+1)+1+1)+1+14+
        (pick (get C) (.lookup C.slot .row) H xs).work+1≤_
      rw [List.length_cons,Nat.succ_mul]
      dsimp [bound] at *
      omega
  apply (one (List.finRange D)).trans
  simp only [List.length_finRange]
  unfold bound
  ring_nf
  omega

theorem cheap_code (C : Chart) (D H w out : ℕ) :
    CheapCode (scan w out (H*D) (code C D H)) := @scan_cheap _ _ _ _

def originValue (D i : ℕ) := i/D*D
def slotValue (D i : ℕ) := i%D

theorem canonical_addresses (v : Fin H) (j : Fin D) :
    originValue D (v.val*D+j.val)=v.val*D ∧ slotValue D (v.val*D+j.val)=j.val := by
  have p:=Nat.zero_lt_of_lt j.isLt
  have host : (v.val*D+j.val)/D=v.val := by
    rw [Nat.mul_comm v.val D,Nat.mul_add_div p,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  constructor
  · exact congrArg (fun a : ℕ=>a*D) host
  · change (v.val*D+j.val)%D=j.val
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]

theorem chart_mounted (C : Chart) (outRank outSlot : ℕ) (m : Memory w) (H D : ℕ)
    (setO : C.origin.base=outRank) (setS : C.slot.base=outSlot)
    (fit : outRank+H*D≤outSlot) (endFit : outSlot+H*D<2^w) :
    let n:=H*D
    let origin:=DescentStaticWordColumn.program w outRank (originValue D) n
    let slots:=DescentStaticWordColumn.program w outSlot (slotValue D) n
    let m₁:=DescentStaticWordColumn.image outRank (originValue D) m n
    let m₂:=DescentStaticWordColumn.image outSlot (slotValue D) m₁ n
    (Procedure.seq origin slots).Exec m m₂ ((4+10*n)+(4+10*n)) ∧
    (∀v : Fin H,∀j : Fin D,m₂ (C.origin.base+(v.val*D+j.val))=((v.val*D:ℕ):Word w)) ∧
    (∀v : Fin H,∀j : Fin D,m₂ (C.slot.base+(v.val*D+j.val))=(j.val:Word w)) ∧
    ∀a<outRank,m₂ a=m a := by
  dsimp only
  have early : outRank+H*D<2^w:=by omega
  let mountedOrigin := DescentStaticWordColumn.image outRank (originValue D) m (H*D)
  have live (v : Fin H) (j : Fin D) : v.val*D+j.val<H*D :=
    (Nat.add_lt_add_left j.isLt _).trans_le (by
      rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ v.isLt)
  refine ⟨Procedure.Exec.then
    (DescentStaticWordColumn.mount outRank (H*D) (originValue D) m early)
    (DescentStaticWordColumn.mount outSlot (H*D) (slotValue D) mountedOrigin endFit),?_,?_,?_⟩
  · intro v j
    have below : outRank+(v.val*D+j.val)<outSlot := (Nat.add_lt_add_left (live v j) outRank).trans_le fit
    rw [setO]
    exact (DescentStaticWordColumn.frame outSlot (H*D) (slotValue D) mountedOrigin _ (.inl below)).trans
      ((DescentStaticWordColumn.read outRank (H*D) (originValue D) m (live v j)).trans
        (congrArg (fun a : ℕ=>(a:Word w)) (canonical_addresses v j).1))
  · intro v j
    rw [setS]
    exact (DescentStaticWordColumn.read outSlot (H*D) (slotValue D) mountedOrigin (live v j)).trans
      (congrArg (fun a : ℕ=>(a:Word w)) (canonical_addresses v j).2)
  · intro a ha
    exact (DescentStaticWordColumn.frame outSlot (H*D) (slotValue D) mountedOrigin a (.inl (by omega))).trans
      (DescentStaticWordColumn.frame outRank (H*D) (originValue D) m a (.inl ha))

end
end Hierarchy.DescentSortedRoster

end OAI
