import OAI.Hierarchy.TaggedWireRoleIndices

namespace OAI
/-! # Comparison of two block numberings on live parallel rows -/
noncomputable section
namespace Hierarchy.WireTelescope.SettledMatrix.Layout
open scoped Classical
variable {E I A C:Type} [Fintype I] [Fintype A] {r ng na:ℕ}
    (edges:E↪Fin r) (g:I≃Fin ng) (a:A≃Fin na)
local notation "Src" => E⊕(I⊕A)
local notation "ext" => edges.sumMap (Function.Embedding.refl (I⊕A))
local notation "ord" => ordinal (r:=r) (I:=I) (A:=A)

/-- Ordinals of a three-part array sorted with the two indicated orders. -/
def blockValue : Src→ℕ :=
  Sum.elim (fun e=>(edges e).val) (Sum.elim (fun i=>r+(g i).val) (fun i=>r+ng+(a i).val))

theorem block_order_on_chord (ch:Src→C)
    (goods:Function.Injective (fun i:I=>ch (.inr (.inl i))))
    (axes:Function.Injective (fun j:A=>ch (.inr (.inr j))))
    (x y:Src) (same:ch x=ch y) :
    blockValue edges g a x<blockValue edges g a y ↔ ord (ext x)<ord (ext y) := by
  rcases x with x|x|x <;> rcases y with y|y|y
  · rfl
  · change (edges x).val<r+(g y).val ↔ (edges x).val<(ordinal (r:=r) (A:=A) (.inr (.inl y))).val
    rw [ordinal_goods]
    have := (edges x).isLt
    omega
  · change (edges x).val<r+ng+(a y).val ↔ (edges x).val<(ordinal (r:=r) (I:=I) (.inr (.inr y))).val
    rw [ordinal_reserve]
    have := (edges x).isLt
    omega
  · change r+(g x).val<(edges y).val ↔ (ordinal (r:=r) (A:=A) (.inr (.inl x))).val<(edges y).val
    rw [ordinal_goods]
    have := (edges y).isLt
    omega
  · obtain rfl:=goods same
    simp
  · change r+(g x).val<r+ng+(a y).val ↔ (ordinal (r:=r) (A:=A) (.inr (.inl x))).val<(ordinal (r:=r) (I:=I) (.inr (.inr y))).val
    rw [ordinal_goods,ordinal_reserve]
    have := (g x).isLt
    have := (Fintype.equivFin I x).isLt
    omega
  · change r+ng+(a x).val<(edges y).val ↔ (ordinal (r:=r) (I:=I) (.inr (.inr x))).val<(edges y).val
    rw [ordinal_reserve]
    have := (edges y).isLt
    omega
  · change r+ng+(a x).val<r+(g y).val ↔ (ordinal (r:=r) (I:=I) (.inr (.inr x))).val<(ordinal (r:=r) (A:=A) (.inr (.inl y))).val
    rw [ordinal_goods,ordinal_reserve]
    have := (g y).isLt
    have := (Fintype.equivFin I y).isLt
    omega
  · obtain rfl:=axes same
    simp

end Hierarchy.WireTelescope.SettledMatrix.Layout
end

end OAI
