import OAI.Computability.BorderVNP.DiagonalCellEntries
import OAI.Computability.BorderVNP.PackedGridCells

/-! # Private assignments inside the boxes of the initial grid

Fix one word on each private fine edge of a cell. The public entry then has a
single tagged term. Summing these terms recovers the actual polynomial cell
table, including all fine assignments that fail a local check.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing MvPolynomial
open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
    {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cell : N.Site → Cell) (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Restriction of a fine table to one fine site in one public box, with
its private wires fixed and its crossing wires read from the public boundary. -/
noncomputable def fineFactor {A : Type*} (table : N.Tables A) (c : Cell)
    (z : N.InsideAssignment cell c) (v : {v : N.Site // cell v = c}) :
    (∀ e : {e : N.CrossingEdge cell //
      cell (N.src e.val) = c ∨ cell (N.dst e.val) = c}, Fin (N.width e.val.val) → Bool) →
    (∀ p : {p : P // cell (N.attach p) = c}, Fin (bits p.val) → Bool) → A :=
  fun a x => table v.val (fun e =>
    if h : cell (N.src e.val) = cell (N.dst e.val) then
      z ⟨e.val, by
        rcases e.property with hs | ht
        · have hs' := (congrArg cell hs).trans v.property
          exact ⟨hs', h.symm.trans hs'⟩
        · have ht' := (congrArg cell ht).trans v.property
          exact ⟨h.trans ht', ht'⟩⟩
    else
      a ⟨⟨e.val,h⟩, e.property.imp (fun hs => (congrArg cell hs).trans v.property)
        (fun ht => (congrArg cell ht).trans v.property)⟩)
    (fun p => x ⟨p.val, (congrArg cell p.property).trans v.property⟩)

variable {Param Gadget E : Type*} [CommSemiring E] (tags : N.Tables (Entry Param Gadget))

/-- The local term before summing the hidden assignments of the fine edges. -/
noncomputable def conditionedCellTags (hidden : ∀ c, N.InsideAssignment cell c) :
    (N.cellNetwork cell position).Tables (Entry Param Gadget) :=
  fun c a x => ∏ v : {v : N.Site // cell v = c}, fineFactor cell tags c (hidden c) v a x

/-- The cell's polynomial table sums the interpreted tagged product over its
own hidden assignment once, independently of the assignments in other boxes. -/
theorem cellTables_eq_local_sum (value : Gadget → E) (c : Cell) (a x) :
    N.cellTables cell position (fun v z y => interpret value (tags v z y)) c a x =
      ∑ h : N.InsideAssignment cell c,
        interpret value (∏ v : {v : N.Site // cell v = c}, fineFactor cell tags c h v a x) := by
  simp only [map_prod]
  rfl

omit [Fintype Cell] [DecidableEq Cell] in
private theorem hidden_read (h : ∀ c, N.InsideAssignment cell c) (e : N.Edge)
    {c d : Cell} (he : c = d) (hc : cell (N.src e) = c ∧ cell (N.dst e) = c)
    (hd : cell (N.src e) = d ∧ cell (N.dst e) = d) :
    h c ⟨e,hc⟩ = h d ⟨e,hd⟩ := by subst d; rfl

/-- The fixed fine assignments give the same local product read using the
physical reassembly of the private wires and the actual crossing assignment. -/
theorem conditionedCellTags_read (z : N.CrossingAssignment cell)
    (h : ∀ c, N.InsideAssignment cell c) (x : Ports bits) (c : Cell) :
    (N.cellNetwork cell position).read (conditionedCellTags cell position tags h) z x c =
      cellEntry N cell tags z h x c := by
  apply Finset.prod_congr rfl
  intro v _
  apply congrArg (fun a => tags v.val a (fun p => x p.val))
  funext e
  by_cases same : cell (N.src e.val) = cell (N.dst e.val)
  · have hc : cell (N.src e.val) = c := by
      rcases e.property with hsrc | hdst
      · exact (congrArg cell hsrc).trans v.property
      · exact same.trans ((congrArg cell hdst).trans v.property)
    simp only [Network.cellAssignmentEquiv, Equiv.coe_fn_symm_mk, dite_eq_left same]
    exact hidden_read cell h _ hc.symm _ _
  · simp only [Network.cellAssignmentEquiv, Equiv.coe_fn_symm_mk, dite_eq_right same]

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
