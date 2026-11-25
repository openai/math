import OAI.Hierarchy.DescentResetLaneIssue
import OAI.Hierarchy.DescentPublicOperandFlatTap

namespace OAI
/-! # The signed-row order of both ends of a rotor tap is the order of the installed public socket -/
namespace Hierarchy.DescentPublicOperandPhysicalPorts
open DescentRouterSlots DescentNamedContact DescentOrderedWords DescentOrderedReset
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {I C R W : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W]
variable {Y N : ℕ} (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W)
local notation "E" => Item contact owner s w
variable (first : InputId site s w↪Fin Y) (last : LinkId owner s w↪Fin Y)
local notation "src" => fun i : E=>first (root contact input site owner s w align i)
local notation "dst" => fun i : E=>last (link contact owner s w i)

def roots (e : E) : {i : E // src i=src e}≃Fibre (input s) (input s e.val) where
  toFun i:=⟨i.val.val,congrArg Subtype.val (first.injective i.property)⟩
  invFun i:=
    let inside : owner s (contact i.val)=w := (align s i.val).symm.trans
      ((congrArg (site s) i.property).trans ((align s e.val).trans e.property))
    ⟨⟨i.val,inside⟩,congrArg first (Subtype.ext i.property)⟩
  left_inv _:=rfl
  right_inv _:=rfl

def links (e : E) : {i : E // dst i=dst e}≃Fibre contact (contact e.val) where
  toFun i:=⟨i.val.val,congrArg Subtype.val (last.injective i.property)⟩
  invFun i:=
    let inside : owner s (contact i.val)=w := (congrArg (owner s) i.property).trans e.property
    ⟨⟨i.val,inside⟩,congrArg last (Subtype.ext i.property)⟩
  left_inv _:=rfl
  right_inv _:=rfl

omit [Fintype C] [Fintype R] [Fintype W] in
theorem root_prefix (key : I↪Fin N) (e : E) :
    (Finset.univ.filter (fun j : {i : E // src i=src e}=>key j.val.val<key e.val)).card=
      (before (fibreKey key (input s) (input s e.val)) ⟨e.val,rfl⟩).card := by
  apply Finset.card_equiv (roots contact input site owner align s w first e)
  intro i
  simp only [before,Finset.mem_filter,Finset.mem_univ,true_and]; rfl

omit [Fintype C] [Fintype W] in
theorem link_prefix (key : I↪Fin N) (e : E) :
    (Finset.univ.filter (fun j : {i : E // dst i=dst e}=>key j.val.val<key e.val)).card=
      (before (fibreKey key contact (contact e.val)) ⟨e.val,rfl⟩).card := by
  apply Finset.card_equiv (links contact owner s w last e)
  intro i
  simp only [before,Finset.mem_filter,Finset.mem_univ,true_and]; rfl

omit [Fintype R] in
theorem root_units (D m p : ℕ) (hp : 0<p) (e : E) :
    DescentNetworkSubstitution.slotWidth (DescentRouterBank.network D contact input site owner (fun _=>m*p)) (s,w)
      (rootSlot D contact input site owner (fun _=>m*p) s w (root contact input site owner s w align e))/p=
        Fintype.card {i : E // src i=src e}*m :=by
  let eqv:=roots contact input site owner align s w first e
  change (∑_i : Fibre (input s) (input s e.val), m*p)/p=_
  rw [Fintype.card_congr eqv]
  simp [←Nat.mul_assoc,Nat.mul_div_cancel _ hp]

omit [Fintype R] in
theorem link_units (D m p : ℕ) (hp : 0<p) (e : E) :
    DescentNetworkSubstitution.slotWidth (DescentRouterBank.network D contact input site owner (fun _=>m*p)) (s,w)
      (linkSlot D contact input site owner (fun _=>m*p) s w (link contact owner s w e))/p=
        Fintype.card {i : E // dst i=dst e}*m :=by
  let eqv:=links contact owner s w last e
  rw [linkWidth,Fintype.card_congr eqv]
  change (∑_i : Fibre contact (contact e.val),m*p)/p=_
  simp [←Nat.mul_assoc,Nat.mul_div_cancel _ hp]

end
end Hierarchy.DescentPublicOperandPhysicalPorts

end OAI
