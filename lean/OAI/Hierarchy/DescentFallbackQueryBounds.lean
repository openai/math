import OAI.Hierarchy.DescentResetPublicOperandBook

namespace OAI
/-! # Numerical bounds on rows of the original public operand ticket directory -/
namespace Hierarchy.DescentFallbackOperandQuery
open DescentResetLocalRoster DescentPrivateTreeTemplate DescentPacking.PackedMatch.Local
noncomputable section

theorem pair_below {i j m n : ℕ} (a : i< m) (b : j<n) : i*n+j< m*n :=by
  calc
    i*n+j < (i+1)*n :=by rw [Nat.add_one_mul];omega
    _ ≤ m*n :=Nat.mul_le_mul_right _ a

theorem directed_le {size position : ℕ} (side : Bool) (at_ : position<size) :
    directed size side position≤2*size :=by
  cases side <;> simp [directed] <;> omega

theorem tree_slot_lt (height depth leaf : ℕ) (bounded : depth≤height) :
    DescentContactReceiver.treeSlot height depth leaf<2^height :=by
  unfold DescentContactReceiver.treeSlot
  split
  · apply Nat.lt_of_lt_of_le (Fin.isLt _)
    exact Nat.pow_le_pow_right (by decide) bounded
  · exact Nat.two_pow_pos _

theorem path_rank_lt {h d leaf slots : ℕ} (positive : 0<slots)
    (size : Fintype.card (Edge h)≤ slots) : pathRank h d leaf<slots :=by
  unfold pathRank
  split
  · split
    · exact (Fin.isLt _).trans_le size
    · exact positive
  · exact positive

end
end Hierarchy.DescentFallbackOperandQuery

namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentResetLocalRoster DescentPrivateTreeTemplate DescentFallbackOperandQuery DescentFallbackItemSelect
noncomputable section
variable (C : Config) {n : ℕ}

theorem stem_bound (side : Bool) (cap : ℕ) (it : Item)
    (res : it.residual<2^C.residual) (port : it.signed<2*cap) :
    C.stemAt side cap it≤2*total C.toShape cap :=by
  apply directed_le
  have slot:=pair_below (finTwoEquiv.symm side).isLt (pair_below res port)
  change _ < 2*(2^C.residual*(2*cap))+(1+_)
  rw [Nat.add_assoc]
  exact slot.trans_le (Nat.le_add_right _ _)

theorem contact_position_bound (side : Bool) (cap : ℕ) (rt : Root C.residual (2^n))
    (port : ℕ) (sectors : C.sectors=2^n) (inside : port<sockets C.toShape) :
    stemSlots C.toShape cap+1+((finTwoEquiv.symm side).val*(rootSlots C.residual (2^n)*sockets C.toShape)+
      (rootId C.residual (2^n) rt).val*sockets C.toShape+port)<total C.toShape cap :=by
  have within:=pair_below (finTwoEquiv.symm side).isLt (pair_below (rootId C.residual (2^n) rt).isLt inside)
  unfold total contactSlots
  rw [sectors]
  omega

theorem contact_bound (side : Bool) (cap depth leaf : ℕ)
    (root : code C.residual×Option (Fin (2^n))) (sectors : C.sectors=2^n) (bounded : depth≤C.maxDepth) :
    C.contactAt side cap depth leaf root≤2*total C.toShape cap :=by
  apply directed_le
  apply C.contact_position_bound side cap (.inr root) _ sectors
  have inside:=tree_slot_lt C.maxDepth depth leaf bounded
  change 2^n+_ < C.sectors+2^C.maxDepth
  omega

theorem tree_bound (side face : Bool) (cap depth d leaf : ℕ) (root : code C.residual×Option (Fin (2^n)))
    (sectors : C.sectors=2^n) (positive : 0<C.privateSlots) (slots : Fintype.card (Edge depth)≤C.privateSlots) :
    C.treeAt side face cap depth d leaf root≤2*total C.toShape cap :=by
  apply directed_le
  have inner:=pair_below (rootId C.residual (2^n) (.inr root)).isLt
    (path_rank_lt (d:=d) (leaf:=leaf/2^(C.maxDepth-depth)) positive slots)
  have outside:=pair_below (finTwoEquiv.symm side).isLt inner
  change stemSlots C.toShape cap+1+contactSlots C.toShape+_ < total C.toShape cap
  unfold total
  rw [sectors]
  omega

end
end Hierarchy.DescentFallbackOperandBranch.Config

end OAI
