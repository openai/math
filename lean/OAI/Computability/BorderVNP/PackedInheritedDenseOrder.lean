import OAI.Computability.BorderVNP.PackedBankInheritedValue

/-! # Virtual-site incidence order under a dense cable save

Compacting the occupied cable rows changes the type of an edge. Each live
edge keeps its original public ID, so the width preceding a loop, crossing
endpoint, or attached port stays the same. This holds for empty words as well.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing CellAddresses
open private endRow from OAI.Computability.BorderVNP.PackedCellAddresses
open scoped Classical

variable {D M np : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
    (rows : N.Edge ↪ Fin M) (portID : P ↪ Fin np) (v : N.Site)

private noncomputable abbrev dense := Names.denseLayout N rows

private theorem source (e : N.Edge) : (dense N rows).src (Names.denseSlot N rows e) = N.src e :=
  Names.src_slot N _ _ e

private theorem dest (e : N.Edge) : (dense N rows).dst (Names.denseSlot N rows e) = N.dst e :=
  Names.dst_slot N _ _ e

/-- A compacted live edge carries every original lane. -/
theorem dense_width (e : N.Edge) : (Names.denseLayout N rows).width (Names.denseSlot N rows e) = N.width e :=
  Names.width_slot N _ _ e

/-- The bijection of live incidence rows, counting a loop only once. -/
noncomputable def denseIncident : Incident N v ≃ Incident (Names.denseLayout N rows) v :=
  (Names.denseSlot N rows).subtypeEquiv (fun e => by
    change (N.src e = v ∨ N.dst e = v) ↔ ((dense N rows).src (Names.denseSlot N rows e) = v ∨ (dense N rows).dst (Names.denseSlot N rows e) = v)
    rw [source,dest])

private noncomputable def inside : N.InsideEdge id v ≃ (dense N rows).InsideEdge id v :=
  (Names.denseSlot N rows).subtypeEquiv (fun e => by
    change (N.src e = v ∧ N.dst e = v) ↔ ((dense N rows).src (Names.denseSlot N rows e) = v ∧ (dense N rows).dst (Names.denseSlot N rows e) = v)
    rw [source,dest])

private noncomputable def crossing : N.CrossingEdge id ≃ (dense N rows).CrossingEdge id :=
  (Names.denseSlot N rows).subtypeEquiv (fun e => by
    change (N.src e ≠ N.dst e) ↔ (dense N rows).src (Names.denseSlot N rows e) ≠ (dense N rows).dst (Names.denseSlot N rows e)
    rw [source,dest])

private noncomputable def boundary : Boundary N id v ≃ Boundary (dense N rows) id v :=
  (crossing N rows).subtypeEquiv (fun e => by
    change (N.src e.val = v ∨ N.dst e.val = v) ↔ ((dense N rows).src (Names.denseSlot N rows e.val) = v ∨ (dense N rows).dst (Names.denseSlot N rows e.val) = v)
    rw [source,dest])

private noncomputable def supplied : Supplied N id v ≃ Supplied (dense N rows) id v :=
  Equiv.sumCongr (boundary N rows v) (Equiv.refl _)

private theorem supplied_width (u : Supplied N id v) :
    suppliedWidth (dense N rows) id v (supplied N rows v u) = suppliedWidth N id v u := by
  rcases u with e|p
  · exact dense_width N rows e.val.val
  · rfl

private theorem publicID (e : N.Edge) : CutCircuit.denseRows N rows (Names.denseSlot N rows e) = rows e :=
  congrArg rows ((Names.denseSlot N rows).symm_apply_apply e)

private theorem supplied_row (u : Supplied N id v) :
    suppliedRow (dense N rows) id v (CutCircuit.denseRows N rows) portID (supplied N rows v u) =
      suppliedRow N id v rows portID u := by
  rcases u with e|p
  · have he : endRow (dense N rows) id v (CutCircuit.denseRows N rows) (boundary N rows v e) =
        endRow N id v rows e := by
      change (if (dense N rows).src (Names.denseSlot N rows e.val.val) = v then
        Sum.inl (CutCircuit.denseRows N rows (Names.denseSlot N rows e.val.val)) else
        Sum.inr (CutCircuit.denseRows N rows (Names.denseSlot N rows e.val.val))) = _
      rw [source,publicID]
      rfl
    exact congrArg (fun k : Fin M ⊕ Fin M =>
      (finSumFinEquiv (Sum.inl (finSumFinEquiv k) : Fin (M+M) ⊕ Fin np)).val) he
  · rfl

private theorem guessed_size :
    guessedSize (dense N rows) id v = guessedSize N id v := by
  unfold guessedSize
  rw [← (inside N rows v).sum_comp]
  exact Finset.sum_congr rfl (fun e _ => dense_width N rows e.val)

variable [Fintype P]

/-- The compacted virtual site has exactly its old incoming bit count. -/
theorem dense_incoming : incoming (Names.denseLayout N rows) v = incoming N v := by
  unfold incoming
  rw [guessed_size N rows v]
  congr 1
  unfold suppliedSize
  rw [← (supplied N rows v).sum_comp]
  exact Finset.sum_congr rfl (fun u _ => supplied_width N rows v u)

private theorem start_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (a : A ↪ ℕ) (b : B ↪ ℕ) (wa : A → ℕ) (wb : B → ℕ)
    (row : ∀ x, b (e x) = a x) (width : ∀ x, wb (e x) = wa x) (x : A) :
    CellSlabs.start b wb (e x) = CellSlabs.start a wa x := by
  unfold CellSlabs.start
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  rw [row x, row y, width y]

private theorem supplied_start (u : Supplied N id v) :
    CellSlabs.start (suppliedRow (dense N rows) id v (CutCircuit.denseRows N rows) portID)
      (suppliedWidth (dense N rows) id v) (supplied N rows v u) =
    CellSlabs.start (suppliedRow N id v rows portID) (suppliedWidth N id v) u :=
  start_equiv (supplied N rows v) _ _ _ _ (supplied_row N rows portID v) (supplied_width N rows v) u

omit [Fintype P] in
private theorem ext_base :
    externalBase (dense N rows) id v (fun _ => 0) = externalBase N id v (fun _ => 0) := by
  simp [externalBase,siteSize,guessed_size N rows v]

/-- The start of a live cable, including a zero-width cable, is invariant under compacting. -/
theorem dense_wireStart (z : Incident N v) :
    wireStart (Names.denseLayout N rows) (CutCircuit.denseRows N rows) portID v (denseIncident N rows v z) =
      wireStart N rows portID v z := by
  unfold wireStart wireBase
  by_cases h : N.src z.val = N.dst z.val
  · have h' : id ((dense N rows).src (denseIncident N rows v z).val) =
        id ((dense N rows).dst (denseIncident N rows v z).val) := (source N rows z.val).trans (h.trans (dest N rows z.val).symm)
    rw [dite_eq_left h',dite_eq_left (show id (N.src z.val) = id (N.dst z.val) from h)]
    have both : N.src z.val = v ∧ N.dst z.val = v := by rcases z.property with hv|hv <;> simp_all
    exact start_equiv (inside N rows v) _ _ _ _ (fun e => congrArg Fin.val (publicID N rows e.val))
      (fun e => dense_width N rows e.val) ⟨z.val,both⟩
  · have h' : id ((dense N rows).src (denseIncident N rows v z).val) ≠
        id ((dense N rows).dst (denseIncident N rows v z).val) :=
        fun eqn => h ((source N rows z.val).symm.trans (eqn.trans (dest N rows z.val)))
    rw [dite_eq_right h',dite_eq_right (show id (N.src z.val) ≠ id (N.dst z.val) from h),ext_base N rows v]
    exact congrArg (_ + ·) (supplied_start N rows portID v (.inl ⟨⟨z.val,h⟩,z.property⟩))

/-- The start of each external port is invariant under compacting the cable array. -/
theorem dense_portStart (u : Attached N v) :
    portStart (Names.denseLayout N rows) (CutCircuit.denseRows N rows) portID v u =
      portStart N rows portID v u := by
  unfold portStart portBase
  rw [ext_base N rows v]
  exact congrArg (_ + ·) (supplied_start N rows portID v (.inr u))

end Packing.Inherited

end BorderVNP
end Computability
end OAI
