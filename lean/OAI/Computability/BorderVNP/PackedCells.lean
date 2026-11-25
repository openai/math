import OAI.Computability.BorderVNP.CrossingNetwork

/-! # Contracting site boxes on a public grid

Proposition 7.2 retains every connection inside one cell in its private box. The only cable
records visible at other cells are the original edges joining distinct cells. This construction
realizes that operation for arbitrary bit widths and over any commutative semiring.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped Classical
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell] (cell : N.Site → Cell)
variable (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Cross-cell cables have both of their ends in the public directory. -/
abbrev CrossingEdge := {e : N.Edge // cell (N.src e) ≠ cell (N.dst e)}

/-- A private cable lives in exactly one local box. -/
abbrev InsideEdge (c : Cell) := {e : N.Edge // cell (N.src e) = c ∧ cell (N.dst e) = c}

/-- Replace the fine sites by their cells, leaving just cross-cell cables exposed. -/
abbrev cellNetwork : Network D P bits where
  Site := Cell
  Edge := N.CrossingEdge cell
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := cell (N.src e.val)
  dst e := cell (N.dst e.val)
  width e := N.width e.val
  attach p := cell (N.attach p)
  position c := (position c).val
  in_ball c := (position c).property

/-- The bit assignments private to a particular cell. -/
abbrev InsideAssignment (c : Cell) := ∀ e : N.InsideEdge cell c, Fin (N.width e.val) → Bool

omit [Fintype Cell] [DecidableEq Cell] in
private theorem bothEnds {v : N.Site} {e : N.Edge} (c : Cell) (hv : cell v = c)
    (he : N.src e = v ∨ N.dst e = v) (same : cell (N.src e) = cell (N.dst e)) :
    cell (N.src e) = c ∧ cell (N.dst e) = c := by
  cases he with
  | inl h => exact ⟨h ▸ hv, same.symm.trans (h ▸ hv)⟩
  | inr h => exact ⟨same.trans (h ▸ hv), h ▸ hv⟩

variable {R : Type*} [CommSemiring R]

/-- Inside a cell, sum all its private cable words once and read all exposed words at their
public endpoints. Only the tables of the fine vertices lying in this cell are used. -/
noncomputable def cellTables (table : N.Tables R) : (N.cellNetwork cell position).Tables R :=
  fun c boundary x =>
    ∑ localBits : N.InsideAssignment cell c,
    ∏ v : {v : N.Site // cell v = c},
      table v.val (fun e =>
        if same : cell (N.src e.val) = cell (N.dst e.val) then
          localBits ⟨e.val, N.bothEnds cell c v.property e.property same⟩
        else
          boundary ⟨⟨e.val, same⟩, by
            rcases e.property with h | h
            · exact Or.inl ((congrArg cell h).trans v.property)
            · exact Or.inr ((congrArg cell h).trans v.property)⟩)
        (fun p => x ⟨p.val, (congrArg cell p.property).trans v.property⟩)

/-- Assignments on the wires that remain exposed in the cell network. -/
abbrev CrossingAssignment := ∀ e : N.CrossingEdge cell, Fin (N.width e.val) → Bool

/-- Splitting all cable assignments into the public cables and the private cables of each
cell is a bijection, including loops and zero-width cables. -/
noncomputable def cellAssignmentEquiv :
    N.Assignment ≃ N.CrossingAssignment cell × (∀ c, N.InsideAssignment cell c) where
  toFun a := (fun e => a e.val, fun _ e => a e.val)
  invFun pair e :=
    if h : cell (N.src e) = cell (N.dst e) then pair.2 _ ⟨e, rfl, h.symm⟩ else pair.1 ⟨e,h⟩
  left_inv a := by
    funext e
    dsimp only
    split <;> rfl
  right_inv pair := by
    apply Prod.ext
    · funext e; simp only [dite_eq_right e.property]
    · funext c e
      have he := e.property.1.trans e.property.2.symm
      dsimp only
      rw [dite_eq_left he]
      obtain ⟨e, hsrc, hdst⟩ := e
      subst c
      rfl

private theorem univ_same {α : Type*} (f g : Fintype α) :
    @Finset.univ α f = @Finset.univ α g := congrArg (@Finset.univ α) (Subsingleton.elim f g)

omit [Fintype Cell] [DecidableEq Cell] in
private theorem read_private_eq (localBits : ∀ c, N.InsideAssignment cell c)
    (edge : N.Edge) {c d : Cell} (h : c = d)
    (hc : cell (N.src edge) = c ∧ cell (N.dst edge) = c)
    (hd : cell (N.src edge) = d ∧ cell (N.dst edge) = d) :
    localBits c ⟨edge, hc⟩ = localBits d ⟨edge, hd⟩ := by subst d; rfl

set_option maxHeartbeats 1000000 in
/-- Grouping the actual local tensors by cells leaves the entire contraction equal for each
setting of its external ports, including when the entries are polynomials in parameters. -/
theorem value_cellNetwork (table : N.Tables R) (x : Ports bits) :
    (N.cellNetwork cell position).value (N.cellTables cell position table) x = N.value table x := by
  classical
  symm
  let e := N.cellAssignmentEquiv cell
  let block (pair : N.CrossingAssignment cell × (∀ c, N.InsideAssignment cell c)) :=
    ∏ c : Cell, ∏ v : {v : N.Site // cell v = c}, N.read table (e.symm pair) x v.val
  calc
    _ = ∑ pair, block pair := by
      apply Fintype.sum_equiv e
      intro a
      simp only [block, Equiv.symm_apply_apply]
      exact (Fintype.prod_fiberwise cell (fun v => N.read table a x v)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      unfold value
      apply Finset.sum_congr
      · exact univ_same _ _
      intro boundary _
      dsimp only [read, cellTables]
      rw [Fintype.prod_sum]
      apply Finset.sum_congr
      · exact univ_same _ _
      intro localBits _
      apply Finset.prod_congr
      · exact univ_same _ _
      intro c _
      apply Finset.prod_congr
      · exact univ_same _ _
      intro v _
      apply congrArg (fun s => table v.val s (fun p => x p.val))
      funext j
      by_cases hj : cell (N.src j.val) = cell (N.dst j.val)
      · dsimp only [e, cellAssignmentEquiv, Equiv.coe_fn_symm_mk]
        rw [dite_eq_left hj, dite_eq_left hj]
        exact N.read_private_eq cell localBits j.val (N.bothEnds cell c v.property j.property hj).1
          ⟨rfl, hj.symm⟩ (N.bothEnds cell c v.property j.property hj)
      · dsimp only [e, cellAssignmentEquiv, Equiv.coe_fn_symm_mk]
        rw [dite_eq_right hj, dite_eq_right hj]

end Crossing.Network

end BorderVNP
end Computability
end OAI
