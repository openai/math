import OAI.Hierarchy.TaggedWideDatedRoleInput
import OAI.Hierarchy.TaggedWireDatedMiddle

namespace OAI
/-! # Reconstructing a preclip source width by reading the two dated spill banks -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleInput
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProtocolRAM Calendar RoleProgram WireTelescope
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing

def floorSub (a b : Expr) : Expr :=
  .branch .lt a b (.lit 0) (.op .sub a b)

def spillMiddle (g : Inventory) (post : Expr) (load wasted : Bank) : Expr :=
  .branch .eq g.kind (.lit 0) (floorSub post (.lookup load g.index))
    (.branch .eq g.kind (.lit 1) (.op .add post (.lookup wasted g.index)) post)

theorem spillMiddle_work (g : Inventory) (post : Expr) (load wasted : Bank) :
    (spillMiddle g post load wasted).work=2*g.kind.work+4*post.work+3*g.index.work+23 := by
  simp only [spillMiddle,floorSub,Expr.work]
  omega

theorem spillMiddle_fits {w out : ℕ} (g : Inventory) (post : Expr) (load wasted : Bank)
    (kind : g.kind.Fits w out) (index : g.index.Fits w out) (state : post.Fits w out)
    (routes : load.Fits w out) (spill : wasted.Fits w out) : (spillMiddle g post load wasted).Fits w out :=
  ⟨kind,trivial,⟨state,⟨routes,index⟩,trivial,⟨state,routes,index⟩⟩,
    kind,trivial,⟨state,spill,index⟩,state⟩

theorem floorSub_read {w : ℕ} (a b : Expr) (m : Memory w) (r : Word w) :
    ((floorSub a b).eval m r).val=(a.eval m r).val-(b.eval m r).val := by
  let u:=a.eval m r
  let v:=b.eval m r
  change (if decide (u<v) then ((0:ℕ):Word w) else u-v).val=u.val-v.val
  by_cases low : u.val<v.val
  · have lt : u<v:=low
    simp only [lt,decide_true,ite_true,Nat.cast_zero,Fin.val_zero,Nat.sub_eq_zero_of_le low.le]
  · have le : v.val≤u.val:=Nat.le_of_not_gt low
    have lt : ¬u<v:=low
    have same : ((u.val-v.val:ℕ):Word w)=u-v:=by
      rw [Nat.cast_sub le,Fin.cast_val_eq_self,Fin.cast_val_eq_self]
    simp only [lt,decide_false,Bool.false_eq_true,ite_false]
    rw [←same,Fin.val_cast_of_lt ((Nat.sub_le ..).trans_lt u.isLt)]

variable {h W k rows w : ℕ}
local notation "I" => Old h W k rows
local notation "rank" => SettledMatrix.Layout.numbered (r:=rows) («I»:=Goods h W k) (A:=Catalysts h W k)

theorem spillMiddle_read (g : Inventory) (post : Expr) (load wasted : Bank)
    (m : Memory w) (i : Fin (Fintype.card I)) (after : I→ℕ)
    (debit : Fin rows→ℕ) (overflow : Goods h W k→ℕ)
    (wide : 2<2^w) (decoded : g.kind.eval m (i.val:Word w)=(tag (rank i):Word w) ∧
      g.index.eval m (i.val:Word w)=(localIndex (rank i):Word w))
    (actual : (post.eval m (i.val:Word w)).val=after (rank i))
    (pay : ∀e,(load.read m (e.val:Word w)).val=debit e)
    (spill : ∀x,(wasted.read m ((PurchaseInventory.slot x):Word w)).val=overflow x)
    (room : ∀x,after (.inr (.inl x))+overflow x<2^w) :
    ((spillMiddle g post load wasted).eval m (i.val:Word w)).val=
      Sum.elim (fun e=>after (.inl e)-debit e)
        (Sum.elim (fun x=>after (.inr (.inl x))+overflow x) (fun a=>after (.inr (.inr a)))) (rank i) := by
  have ne:=codes wide
  rcases shape : rank i with e|x|a
  · simp only [shape,tag,localIndex] at decoded
    simp only [shape] at actual
    change ((if Comparison.eq.test (g.kind.eval m _) (((0:ℕ):Word w)) then _ else _):Word w).val=_
    simp only [Comparison.test, decoded.1, beq_iff_eq, ite_true, Sum.elim_inl]
    rw [floorSub_read,actual]
    change _-(load.read m (g.index.eval m _)).val=_
    rw [decoded.2,pay]
  · simp only [shape,tag,localIndex] at decoded
    simp only [shape] at actual
    have changeWord : ((post.eval m (i.val:Word w))+(wasted.read m ((PurchaseInventory.slot x):Word w))).val=
        after (.inr (.inl x))+overflow x:=by
      rw [Fin.val_add,actual,spill,Nat.mod_eq_of_lt (room x)]
    simpa [spillMiddle,Expr.eval,Comparison.test,RowOp.opcode,BinaryOp.eval,decoded.1,decoded.2,ne.1] using changeWord
  · simp only [shape,tag,localIndex] at decoded
    simp only [shape] at actual
    simpa [spillMiddle,Expr.eval,Comparison.test,decoded.1,ne.2.1,ne.2.2] using actual

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleInput
end

end OAI
