import OAI.Computability.BorderVNP.PackedFinalTieNatural

/-! # Actual cell bank addresses under an injective public numbering -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Merged.CellKey

open Crossing Packing Packing.Inherited Packing.CellAddresses
open private endRow from OAI.Computability.BorderVNP.PackedCellAddresses
open private offset from OAI.Computability.BorderVNP.PackedInheritedPlacementTies
open private start_congr from OAI.Computability.BorderVNP.PackedFinalTieNatural
open scoped Classical

variable {D s m np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (code : C ↪ ℕ) (c : C)
local notation3 "key" => fun v => code (cell v)

private def inside : N.InsideEdge key (code c) ≃ N.InsideEdge cell c :=
  Equiv.subtypeEquivRight fun _ => by simp only [code.injective.eq_iff]

private def boundary : Boundary N key (code c) ≃ Boundary N cell c where
  toFun e := ⟨⟨e.val.val,fun h => e.val.property (congrArg code h)⟩,
    e.property.imp (fun h => code.injective h) (fun h => code.injective h)⟩
  invFun e := ⟨⟨e.val.val,fun h => e.val.property (code.injective h)⟩,
    e.property.imp (congrArg code) (congrArg code)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def supplied : Supplied N key (code c) ≃ Supplied N cell c :=
  Equiv.sumCongr (boundary N cell code c) (Equiv.subtypeEquivRight fun _ => code.injective.eq_iff)

variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin np) (state : N.Site → Site)
local notation3 "size" => fun u => (state u).size

omit [Fintype P] in
private theorem supplied_number (t : Supplied N key (code c)) :
    suppliedRow N key (code c) edgeID portID t = suppliedRow N cell c edgeID portID (supplied N cell code c t) := by
  rcases t with e | p
  · have ends : endRow N key (code c) edgeID e = endRow N cell c edgeID (boundary N cell code c e) := by
      simp only [endRow,Function.Embedding.coeFn_mk,boundary,Equiv.coe_fn_mk,code.injective.eq_iff]
      by_cases h : cell (N.src e.val.val) = c <;> simp [h]
    exact congrArg (fun z : Fin m ⊕ Fin m => ((finSumFinEquiv (Sum.inl (finSumFinEquiv z) :
      Fin (m+m) ⊕ Fin np)) : ℕ)) ends
  · rfl

omit [Fintype P] in
private theorem supplied_start (i : Fintype (Supplied N key (code c))) (j : Fintype (Supplied N cell c))
    (t : Supplied N key (code c)) :
    @CellSlabs.start _ i (suppliedRow N key (code c) edgeID portID) (suppliedWidth N key (code c)) t =
      @CellSlabs.start _ j (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) (supplied N cell code c t) :=
  @start_congr _ _ i j (supplied N cell code c) _ _ _ _ (supplied_number N cell code c edgeID portID)
    (fun z => by cases z <;> rfl) t

/-- Numeric private and supplied bank sizes are independent of the injective cell name. -/
theorem bankSizes : guessedSize N key (code c)=guessedSize N cell c ∧ siteSize N key (code c) size=siteSize N cell c size ∧
    suppliedSize N key (code c)=suppliedSize N cell c := by
  refine ⟨?_,?_,?_⟩
  · unfold guessedSize
    convert! Fintype.sum_equiv (inside N cell code c) (fun e => N.width e.val) (fun e => N.width e.val)
      (fun _ => rfl) using 1
    exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)
  · let eqv : {v : N.Site // key v=code c} ≃ {v : N.Site // cell v=c} :=
      Equiv.subtypeEquivRight fun _ => code.injective.eq_iff
    unfold siteSize
    convert! Fintype.sum_equiv eqv (fun v => (state v.val).size) (fun v => (state v.val).size) (fun _ => rfl)
      using 1
    exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)
  · unfold suppliedSize
    convert! Fintype.sum_equiv (supplied N cell code c) (suppliedWidth N key (code c)) (suppliedWidth N cell c)
      (fun z => by cases z <;> rfl) using 1
    exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)

/-- First address of the supplied bank after internal wires and site slabs. -/
theorem external : externalBase N key (code c) size = externalBase N cell c size := by
  obtain ⟨g,s,_⟩ := bankSizes N cell code c state
  exact congrArg₂ Nat.add g s

/-- First address of a selected site slab after an injective renaming. -/
theorem site (v : {v : N.Site // cell v = c}) :
    siteBase N key (code c) siteID size ⟨v.val,congrArg code v.property⟩ = siteBase N cell c siteID size v := by
  let eqv : {v : N.Site // (code (cell v)) = (code c)} ≃ {v : N.Site // cell v = c} :=
    Equiv.subtypeEquivRight fun _ => code.injective.eq_iff
  apply congrArg₂ Nat.add (bankSizes N cell code c state).1
  apply @start_congr _ _ _ _ eqv <;> intro _ <;> rfl

private theorem wire (v : {v : N.Site // cell v = c}) (e : Incident N v.val) :
    wireBase N key (code c) edgeID portID size ⟨v.val,congrArg code v.property⟩ e =
      wireBase N cell c edgeID portID size v e := by
  by_cases h : cell (N.src e.val) = cell (N.dst e.val)
  · simp only [wireBase,h,dite_true]
    apply @start_congr _ _ _ _ (inside N cell code c) <;> intro _ <;> rfl
  · have hn : code (cell (N.src e.val)) ≠ code (cell (N.dst e.val)) := fun H => h (code.injective H)
    simp only [wireBase,h,hn,dite_false]
    apply congrArg₂ Nat.add (external N cell code c state)
    apply supplied_start N cell code c edgeID portID

private theorem port (v : {v : N.Site // cell v = c}) (p : Attached N v.val) :
    portBase N key (code c) edgeID portID size ⟨v.val,congrArg code v.property⟩ p =
      portBase N cell c edgeID portID size v p := by
  apply congrArg₂ Nat.add (external N cell code c state)
  apply supplied_start N cell code c edgeID portID

/-- The natural-labelled private cell binding and the finite-labelled physical emitter have
the same entire record list, including empty incidences and both classes of cable endpoints. -/
theorem binding_key (v : N.Site) :
    Placement.ties N key (code (cell v)) siteID edgeID portID state ⟨v,rfl⟩ =
      Placement.ties N cell (cell v) siteID edgeID portID state ⟨v,rfl⟩ := by
  unfold Placement.ties
  apply List.map_congr_left
  intro r _
  have hs := site N cell code (cell v) siteID state ⟨v,rfl⟩
  rcases r with e | p
  · have hw := wire N cell code (cell v) edgeID portID state ⟨v,rfl⟩ e
    simp only [Placement.tie,offset,Placement.physicalStart,Sum.elim_inl,hs,hw]
  · have hp := port N cell code (cell v) edgeID portID state ⟨v,rfl⟩ p
    simp only [Placement.tie,offset,Placement.physicalStart,Sum.elim_inr,hs,hp]

end FiniteEvaluator.Merged.CellKey

end BorderVNP
end Computability
end OAI
