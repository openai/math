import OAI.Hierarchy.DescentFixedExceptionalRouter

namespace OAI
/-! # Each physical equality comparison in the exceptional router has a paid input bit -/

namespace Hierarchy.DescentFixedExceptionalRouter
open Computability.BorderVNP.Crossing DescentNetworkSubstitution DescentRouterSlots DescentContactTree
open scoped BigOperators Classical
noncomputable section

variable {I C R V : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype V]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→V) (owner : Bool→C→V) (wt : I→ℕ)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : V)
variable {depth : ℕ} (book : LinkId owner s w ↪ Node depth)

local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "deviceHere" => device D contact input site owner wt s w book
local notation "cost" => amount contact owner wt s w
local notation "dest" => DescentFixedNamedContact.code book (link contact owner s w)
local notation "port" => Slot B (s,w)
local notation "lens" => slotWidth B (s,w)
local notation "pin" => rootSlot D contact input site owner wt s w

private theorem mapped_le {X Y : Type*} [Fintype X] [Fintype Y] (e : X↪Y) (f : Y→ℕ) :
    (∑x,f (e x))≤∑y,f y := by
  classical
  simpa only [Finset.sum_map] using Finset.sum_le_sum_of_subset (f:=f) (Finset.subset_univ (Finset.univ.map e))

include align in
private theorem root_pins (v : Node 0) : Physical.nodeWidth dest cost 0 v≤∑r,lens (pin r) := by
  let U := Σr : InputId site s w,DescentNamedContact.Fibre (input s) r.val
  let key : Cell dest 0 v ↪ U := {
    toFun := fun i=>⟨DescentRouterSlots.root contact input site owner s w align i.val,⟨i.val.val,rfl⟩⟩
    inj' := fun x y eqn=>Subtype.ext (Subtype.ext (congrArg (fun t : U=>t.2.val) eqn))}
  have cap := mapped_le key (fun t : U=>wt t.2.val)
  change Physical.nodeWidth dest cost 0 v≤∑r : InputId site s w,∑i : DescentNamedContact.Fibre (input s) r.val,wt i.val
  calc
    _ ≤ ∑ t : U, wt t.2.val := cap
    _ = _ := Fintype.sum_sigma (fun t : U => wt t.2.val)

include align in
private theorem root_load (v : Node 0) : Physical.nodeWidth dest cost 0 v≤portLoad (deviceHere) ⟨0,v⟩ := by
  let pos : (deviceHere).Site := ⟨0,v⟩
  let emit : InputId site s w ↪ port := {
    toFun := pin
    inj' := fun x y eqn=>Sum.inl.inj (by
      simpa only [names_root] using congrArg (names D contact input site owner wt s w) eqn)}
  have hit (r : InputId site s w) : (deviceHere).attach (emit r)=pos := by
    have idv : v=finZeroElim := Subsingleton.elim _ _
    subst v
    rfl
  let payment := fun p : port=>if (deviceHere).attach p=pos then lens p else 0
  have paid := mapped_le emit payment
  have roots (r : InputId site s w) : payment (emit r)=lens (pin r) := by simp only [payment,hit,ite_true]; rfl
  simp_rw [roots] at paid
  change _≤portLoad (deviceHere) pos
  rw [portLoad_eq]
  exact ((root_pins D contact input site owner wt align s w book v).trans paid).trans
    ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))

private theorem child_load (j : Fin depth) (v : Node (j.val+1)) :
    Physical.nodeWidth dest cost (j.val+1) v≤portLoad (deviceHere) ⟨j.succ,v⟩ := by
  let atCell : (deviceHere).Site := ⟨j.succ,v⟩
  let edge : (deviceHere).Edge := ⟨j,v⟩
  let arrives (e : (deviceHere).Edge) := if (deviceHere).dst e=atCell then (deviceHere).width e else 0
  have localPrice : arrives edge=Physical.nodeWidth dest cost (j.val+1) v := by
    change (if atCell=atCell then Physical.nodeWidth dest cost (j.val+1) v else 0)=_
    rw [ite_eq_left rfl]
  have one : arrives edge≤∑e,arrives e := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ edge)
  change _≤portLoad (deviceHere) atCell
  rw [←localPrice,portLoad_eq]
  exact one.trans (Nat.le_add_left ..)

include align in
/-- At positive depth the cell reads the actual cable arriving at it. At zero depth
all its comparison bits occur in distinct bits of the installed root input slots. -/
theorem nodeWidth_le_portLoad (q : Physical.Site depth) :
    Physical.nodeWidth dest cost q.1.val q.2 ≤ portLoad (deviceHere) q := by
  obtain ⟨j,v⟩ := q
  apply Fin.cases (motive:=fun j : Fin (depth+1)=>∀v : Node j.val,
    Physical.nodeWidth dest cost j.val v≤portLoad (deviceHere) ⟨j,v⟩)
    (root_load D contact input site owner wt align s w book)
    (child_load D contact input site owner wt s w book) j v

end
end Hierarchy.DescentFixedExceptionalRouter

end OAI
