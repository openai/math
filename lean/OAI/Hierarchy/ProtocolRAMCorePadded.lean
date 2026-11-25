import OAI.Hierarchy.ProtocolRAMCoreEdgeLookup

namespace OAI
/-! All entries of the padded native ROM carry a true core ordinal or its sentinel. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
variable {S : PurchaseSampler} {h d k w R : ℕ}

theorem resolve_radius_outside (S : PurchaseSampler) (h d k : ℕ) (axis : Fin k)
    (side : Bool) (j : ℕ) (outside : Fintype.card (Columns h d) ≤ j) :
    resolve S h d k (radius axis side) j = none := by
  change (if fit : j<Fintype.card (Columns h d) then
    some (.inl (.inl ((Fintype.equivFin _).symm ⟨j,fit⟩,axis,side))) else none) = (none:Option (Edges S h d k))
  rw [dite_eq_right (Nat.not_lt.mpr outside)]

def Padded (base : ℕ) (order : Fin R≃Edges S h d k) (m : Memory w) : Prop :=
  ∀ (t : Channel S.degree (Stages h d) k) (j : Fin (stride h d)),
    m ((bank (S:=S) (h:=h) (d:=d) base t).base+j.val)=(cell order t j.val:Word w)

theorem mount_padded (base : ℕ) (order : Fin R≃Edges S h d k) (m : Memory w) : Padded base order (mount base order m) := by
  intro t j
  let n:=((Fintype.equivFin _) t).val
  have hi : n<Fintype.card (Channel S.degree (Stages h d) k) := ((Fintype.equivFin _) t).isLt
  have lo : j.val< stride h d := j.isLt
  have pos := Nat.zero_lt_of_lt lo
  have block := Nat.mul_le_mul_right (stride h d) hi
  rw [Nat.succ_mul] at block
  have inside : base≤base+n*stride h d+j.val ∧ base+n*stride h d+j.val<base+words S h d k := by unfold words;omega
  have div : (n*stride h d+j.val)/stride h d=n := by
    rw [Nat.mul_comm n,Nat.mul_add_div pos,Nat.div_eq_of_lt lo,Nat.add_zero]
  have mod : (n*stride h d+j.val)%stride h d=j.val := Nat.mul_add_mod_of_lt lo
  change mount base order m (base+n*stride h d+j.val)=_
  rw [mount,fillSegment,ite_eq_left inside]
  simp only [Nat.add_assoc,Nat.add_sub_cancel_left,div,mod,dite_eq_left hi]
  simp [n]

theorem padded_inside (base : ℕ) (kind : Channel S.degree (Stages h d) k) (j : Fin (stride h d)) :
    base≤(bank (S:=S) (h:=h) (d:=d) base kind).base+j.val ∧
      (bank (S:=S) (h:=h) (d:=d) base kind).base+j.val<base+words S h d k := by
  have order := Nat.mul_le_mul_right (stride h d) ((Fintype.equivFin _) kind).isLt
  rw [Nat.succ_mul] at order
  have fit : j.val< stride h d := j.isLt
  dsimp only [bank,words];omega

theorem Padded.frame {base : ℕ} {order : Fin R≃Edges S h d k} {m m' : Memory w}
    (loaded : Padded base order m) (stable : ∀ x,base≤x→x<base+words S h d k→m' x=m x) :
    Padded base order m' := fun kind j=>
  (stable _ (padded_inside base kind j).1 (padded_inside base kind j).2).trans (loaded kind j)

theorem Padded.loaded {base : ℕ} {order : Fin R≃Edges S h d k} {m : Memory w}
    (H : Padded base order m) : Loaded base order m :=
  fun t j=>H t ⟨j.val,j.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)⟩

theorem Padded.radius_cases {base : ℕ} {order : Fin R≃Edges S h d k} {m : Memory w}
    (H : Padded base order m) (axis : Fin k) (side : Bool) (key : Expr) (row : Word w) :
    let read := (field (S:=S) (h:=h) (d:=d) base (radius axis side) key).eval m row
    (∃ c : Columns h d, read=((order.symm (.inl (.inl (c,axis,side)))).val:Word w)) ∨ read=(R:Word w) := by
  let n:=stride h d
  have pos : 0<n:=Nat.zero_lt_of_lt (ProtocolRAMPurchaseSampler.lt_span (positions h d))
  let i : Fin n := ⟨(key.eval m row).val % n,Nat.mod_lt _ pos⟩
  intro read
  have atCell : read=(cell order (radius axis side) i.val:Word w):=H _ i
  by_cases small : i.val<Fintype.card (Columns h d)
  · let c:=(Fintype.equivFin (Columns h d)).symm ⟨i.val,small⟩
    have num:((Fintype.equivFin _) c).val=i.val:=congrArg Fin.val ((Fintype.equivFin _).apply_symm_apply _)
    refine Or.inl ⟨c,atCell.trans ?_⟩
    rw [cell,←num,resolve_radius]
    rfl
  · right
    rw [atCell,cell,resolve_radius_outside _ _ _ _ _ _ _ (Nat.le_of_not_gt small)]
    rfl

end Hierarchy.ProtocolRAM.Calendar.CoreLookup
end

end OAI
