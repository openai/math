import OAI.Computability.BorderVNP.PackedFinalReportTemplate
import OAI.Computability.BorderVNP.PackedInheritedPlacementTies

/-! # Finite cell keys and the physical addresses of final binding records

Passing to the natural numeral of a finite cell preserves the start of each guessed cable,
each site slab, each crossing endpoint and each attached external port. The comparison
is on the start itself, including the start of a word of width zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing CellAddresses
open private endRow from OAI.Computability.BorderVNP.PackedCellAddresses
open private offset from OAI.Computability.BorderVNP.PackedInheritedPlacementTies
open scoped Classical

private theorem start_congr {A B : Type*} (i : Fintype A) (j : Fintype B) (f : A ≃ B)
    (a : A ↪ ℕ) (b : B ↪ ℕ) (u : A → ℕ) (v : B → ℕ)
    (rows : ∀ z, a z = b (f z)) (widths : ∀ z, u z = v (f z)) (z : A) :
    @CellSlabs.start _ i a u z = @CellSlabs.start _ j b v (f z) := by
  let _ := i
  let _ := j
  unfold CellSlabs.start
  apply Fintype.sum_equiv f
  intro t
  rw [rows t,rows z,widths t]

variable {D s m np C : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (c : Fin C)
local notation3 "key" => fun v => (cell v).val

private def inside : N.InsideEdge key c.val ≃ N.InsideEdge cell c :=
  Equiv.subtypeEquivRight fun _ => by simp only [Fin.val_inj]

private def boundary : Boundary N key c.val ≃ Boundary N cell c where
  toFun e := ⟨⟨e.val.val,fun h => e.val.property (congrArg Fin.val h)⟩,
    e.property.imp (fun h => Fin.ext h) (fun h => Fin.ext h)⟩
  invFun e := ⟨⟨e.val.val,fun h => e.val.property (Fin.ext h)⟩,
    e.property.imp (congrArg Fin.val) (congrArg Fin.val)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def supplied : Supplied N key c.val ≃ Supplied N cell c :=
  Equiv.sumCongr (boundary N cell c) (Equiv.subtypeEquivRight fun _ => Fin.val_inj)

variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin np) (state : N.Site → Site)
local notation3 "size" => fun u => (state u).size

omit [Fintype P] in
private theorem supplied_number (t : Supplied N key c.val) :
    suppliedRow N key c.val edgeID portID t = suppliedRow N cell c edgeID portID (supplied N cell c t) := by
  rcases t with e | p
  · have ends : endRow N key c.val edgeID e = endRow N cell c edgeID (boundary N cell c e) := by
      simp only [endRow,Function.Embedding.coeFn_mk,boundary,Equiv.coe_fn_mk,Fin.val_inj]
      by_cases h : cell (N.src e.val.val) = c <;> simp [h]
    exact congrArg (fun z : Fin m ⊕ Fin m => ((finSumFinEquiv (Sum.inl (finSumFinEquiv z) :
      Fin (m+m) ⊕ Fin np)) : ℕ)) ends
  · rfl

omit [Fintype P] in
private theorem supplied_start (i : Fintype (Supplied N key c.val)) (j : Fintype (Supplied N cell c))
    (t : Supplied N key c.val) :
    @CellSlabs.start _ i (suppliedRow N key c.val edgeID portID) (suppliedWidth N key c.val) t =
      @CellSlabs.start _ j (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) (supplied N cell c t) :=
  @start_congr _ _ i j (supplied N cell c) _ _ _ _ (supplied_number N cell c edgeID portID)
    (fun z => by cases z <;> rfl) t

private theorem external : externalBase N key c.val size = externalBase N cell c size := by
  obtain ⟨g,s,_⟩ := FinalReports.bank_sizes N cell state c
  exact congrArg₂ Nat.add g s

private theorem site (v : {v : N.Site // cell v = c}) :
    siteBase N key c.val siteID size ⟨v.val,congrArg Fin.val v.property⟩ = siteBase N cell c siteID size v := by
  let eqv : {v : N.Site // (cell v).val = c.val} ≃ {v : N.Site // cell v = c} :=
    Equiv.subtypeEquivRight fun _ => Fin.val_inj
  apply congrArg₂ Nat.add (FinalReports.bank_sizes N cell state c).1
  apply @start_congr _ _ _ _ eqv <;> intro _ <;> rfl

private theorem wire (v : {v : N.Site // cell v = c}) (e : Incident N v.val) :
    wireBase N key c.val edgeID portID size ⟨v.val,congrArg Fin.val v.property⟩ e =
      wireBase N cell c edgeID portID size v e := by
  by_cases h : cell (N.src e.val) = cell (N.dst e.val)
  · simp only [wireBase,h,dite_true]
    apply @start_congr _ _ _ _ (inside N cell c) <;> intro _ <;> rfl
  · have hn : (cell (N.src e.val)).val ≠ (cell (N.dst e.val)).val := fun H => h (Fin.ext H)
    simp only [wireBase,h,hn,dite_false]
    apply congrArg₂ Nat.add (external N cell c state)
    apply supplied_start N cell c edgeID portID

private theorem port (v : {v : N.Site // cell v = c}) (p : Attached N v.val) :
    portBase N key c.val edgeID portID size ⟨v.val,congrArg Fin.val v.property⟩ p =
      portBase N cell c edgeID portID size v p := by
  apply congrArg₂ Nat.add (external N cell c state)
  apply supplied_start N cell c edgeID portID

/-- The natural-labelled private cell binding and the finite-labelled physical emitter have
the same entire record list, including empty incidences and both classes of cable endpoints. -/
theorem binding_nat (v : N.Site) :
    Placement.ties N key (cell v).val siteID edgeID portID state ⟨v,rfl⟩ =
      Placement.ties N cell (cell v) siteID edgeID portID state ⟨v,rfl⟩ := by
  unfold Placement.ties
  apply List.map_congr_left
  intro r _
  have hs := site N cell (cell v) siteID state ⟨v,rfl⟩
  rcases r with e | p
  · have hw := wire N cell (cell v) edgeID portID state ⟨v,rfl⟩ e
    simp only [Placement.tie,offset,Placement.physicalStart,Sum.elim_inl,hs,hw]
  · have hp := port N cell (cell v) edgeID portID state ⟨v,rfl⟩ p
    simp only [Placement.tie,offset,Placement.physicalStart,Sum.elim_inr,hs,hp]

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
