import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # Rewriting the group words of unoccupied native records -/

noncomputable section
namespace Hierarchy.ProtocolRAMReportedPorts
open scoped Classical BigOperators
variable {n : ℕ} (rows : Fin n→Row) (group : Fin n→ℕ) (w m γ g : ℕ)

def regroup (j : Fin n) : Row := {rows j with group:=group j}

variable (active : ∀j,0<pieces rows w j → group j=(rows j).group)
include active

private theorem regroup_sum (take : Fin n→Prop) [DecidablePred take] :
    (∑j : InGroup (regroup rows group) w m γ g,if take j.val then pieces rows w j.val else 0)=
      ∑j : InGroup rows w m γ g,if take j.val then pieces rows w j.val else 0 := by
  classical
  let weight (j : Fin n):=if take j then pieces rows w j else 0
  let widthClass (j : Fin n):=TaggedShorterBudget.widthIndex m ((rows j).width/(w:ℝ))=γ
  let lhs (j : Fin n):=group j=g ∧ widthClass j
  let rhs (j : Fin n):=(rows j).group=g ∧ widthClass j
  change (∑j : {j : Fin n // lhs j},weight j.val)=(∑j : {j : Fin n // rhs j},weight j.val)
  rw [←Finset.sum_subtype (Finset.univ.filter lhs) (fun _=>by simp) weight,
    ←Finset.sum_subtype (Finset.univ.filter rhs) (fun _=>by simp) weight]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases live : 0<pieces rows w j
  · have agree : lhs j ↔ rhs j:=by simp only [lhs,rhs,active j live]
    simp only [agree]
  · have zero : pieces rows w j=0:=by omega
    simp [weight,zero]

theorem regroup_count :
    count (regroup rows group) w m γ g=count rows w m γ g := by
  simpa only [ite_true,count,pieces,regroup] using regroup_sum rows group w m γ g active (fun _=>True)

def regroup_units : Unit rows w m γ g ≃ Unit (regroup rows group) w m γ g where
  toFun u:=⟨⟨u.1.val,by
    change group u.1.val=g ∧ _
    exact ⟨(active _ (Nat.zero_lt_of_lt u.2.isLt)).trans u.1.property.1,u.1.property.2⟩⟩,u.2⟩
  invFun u:=⟨⟨u.1.val,by
    exact ⟨(active _ (Nat.zero_lt_of_lt u.2.isLt)).symm.trans u.1.property.1,u.1.property.2⟩⟩,u.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem regroup_common (distinct : Function.Injective fun j=>(rows j).link) (u : Unit rows w m γ g) :
    Fin.cast (regroup_count rows group w m γ g active).symm (common rows w m γ g distinct u)=
      common (regroup rows group) w m γ g distinct (regroup_units rows group w m γ g active u) := by
  apply Fin.ext
  change ProtocolRAMPortRanks.«prefix» (slotCount rows w m γ g) (fun j=>(rows j.val).link) u.1+u.2.val =
    ProtocolRAMPortRanks.«prefix» (slotCount (regroup rows group) w m γ g)
      (fun j=>(rows j.val).link) ((regroup_units rows group w m γ g active u).1)+u.2.val
  apply congrArg (fun a:ℕ=>a+u.2.val)
  have rowAt : ((regroup_units rows group w m γ g active) u).1.val=u.1.val := rfl
  have samePieces (j : Fin n) : pieces (regroup rows group) w j=pieces rows w j := rfl
  simpa only [ProtocolRAMPortRanks.«prefix»,Finset.sum_filter,slotCount,rowAt,samePieces] using
    (regroup_sum rows group w m γ g active (fun j=>(rows j).link<(rows u.1.val).link)).symm

theorem regroup_common_symm (distinct : Function.Injective fun j=>(rows j).link)
    (i : Fin (count rows w m γ g)) :
    (common (regroup rows group) w m γ g distinct).symm
      (Fin.cast (regroup_count rows group w m γ g active).symm i)=
      regroup_units rows group w m γ g active ((common rows w m γ g distinct).symm i) := by
  apply (common (regroup rows group) w m γ g distinct).injective
  simpa only [Equiv.apply_symm_apply] using
    regroup_common rows group w m γ g active distinct ((common rows w m γ g distinct).symm i)

end Hierarchy.ProtocolRAMReportedPorts

namespace Hierarchy.Tagged.WideStack
open ProtocolRAMReportedPorts
open scoped Classical

set_option maxHeartbeats 1600000 in
theorem regroup_portDistinct {n ports : ℕ} (rows : Fin n→ProtocolRAMEmit.Row) (group : Fin n→ℕ)
    (w m γ g : ℕ) (active : ∀j,0<pieces rows w j → group j=(rows j).group)
    (old new : Fin n→Fin ports) (agree : ∀j,0<pieces rows w j→new j=old j)
    (unique : PortDistinct rows w m γ g old) :
    PortDistinct (regroup rows group) w m γ g new := by
  intro i hi j hj eqn
  change 0 < pieces rows w i.val at hi
  change 0 < pieces rows w j.val at hj
  change new i.val=new j.val at eqn
  have back (v : InGroup (regroup rows group) w m γ g) (live : 0 < pieces rows w v.val) :
      (rows v.val).group=g ∧ TaggedShorterBudget.widthIndex m ((rows v.val).width/(w:ℝ))=γ :=
    ⟨(active v.val live).symm.trans v.property.1,v.property.2⟩
  let a : InGroup rows w m γ g := ⟨i.val,back i hi⟩
  let b : InGroup rows w m γ g := ⟨j.val,back j hj⟩
  have eq : old i.val=old j.val := (agree i.val hi).symm.trans (eqn.trans (agree j.val hj))
  have h : a=b := @unique a hi b hj eq
  exact Subtype.ext (congrArg (fun z : InGroup rows w m γ g => z.val) h)

set_option maxHeartbeats 1600000 in
/-- Both installations publish every occupied rank at the same actual physical port. -/
theorem regroup_placement {n groups ports lanes D w m γ : ℕ} (rows : Fin n→ProtocolRAMEmit.Row)
    (group : Fin n→ℕ) (active : ∀j,0<pieces rows w j → group j=(rows j).group)
    (distinct : Function.Injective fun j=>(rows j).link) (g : Fin groups)
    (old new : Bool→Fin n→Fin ports)
    (agree : ∀b j,0<pieces rows w j→new b j=old b j)
    (oldInj : ∀b,PortDistinct rows w m γ g.val (old b))
    (newInj : ∀b,PortDistinct (regroup rows group) w m γ g.val (new b))
    (room : ∀j,pieces rows w j≤lanes) (fit : ports*lanes≤D) (b : Bool)
    (i : Fin (count rows w m γ g.val)) :
    staticUnit (regroup rows group) g new newInj room fit b
      ((common (regroup rows group) w m γ g.val distinct).symm
        (Fin.cast (regroup_count rows group w m γ g.val active).symm i))=
    staticUnit rows g old oldInj room fit b ((common rows w m γ g.val distinct).symm i) := by
  let u:=(common rows w m γ g.val distinct).symm i
  have rank:=regroup_common rows group w m γ g.val active distinct u
  rw [show common rows w m γ g.val distinct u=i from Equiv.apply_symm_apply _ _] at rank
  rw [rank,Equiv.symm_apply_apply]
  change fixedSlot fit (new b u.1.val,Fin.castLE (room _) u.2)=
    fixedSlot fit (old b u.1.val,Fin.castLE (room _) u.2)
  rw [agree b u.1.val (Nat.zero_lt_of_lt u.2.isLt)]

end Hierarchy.Tagged.WideStack
end

end OAI
