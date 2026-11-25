import OAI.Computability.BorderVNP.DiagonalInitialGridCells

/-! # Tagged terms at the publicly addressed grid boxes

A private assignment of every fine in-cell wire gives one term on the uniform
grid. Padding of the public channels is a local zero-one test. Summing over all
private assignments gives the original fine contraction.
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
    {Q : Type} [Fintype Q] {src dst : Q → Cell} {H : ℕ}
    (packing : (N.cellNetwork cell position).ChannelPacking src dst H)

section Uniform
variable {M : Network D P bits} {origin finish : Q → M.Site} {S : ℕ}
    (c : M.ChannelPacking origin finish S)

/-- Restrict a local public cable word to the private subword used by each
incident edge. The site reads only its own ends, even at a loop. -/
noncomputable def unpackFactor {A : Type*} (f : M.Tables A) :
    (M.uniformGrid origin finish S).Tables A :=
  fun v a x => f v (fun e i => a ⟨c.channel e.val,
    e.property.imp ((c.src_eq e.val).trans) ((c.dst_eq e.val).trans)⟩ (c.address ⟨e.val,i⟩).2) x

/-- The per-box padding check at its actual public channel incidences. -/
def padOK : (M.uniformGrid origin finish S).Tables Prop :=
  fun _ a _ => ∀ q, c.ZeroPad q.val (a q)

/-- A private tagged term read from the public padded words, or zero at a failed pad check. -/
noncomputable def paddedFactor {A : Type*} [Zero A] (f : M.Tables A) :
    (M.uniformGrid origin finish S).Tables A :=
  fun v a x => if padOK c v a x then unpackFactor c f v a x else 0

variable {Param Gadget E : Type*} [CommSemiring E] (values : Gadget → E)

/-- Interpreting a single padded tagged term commutes with the public channel decoder. -/
theorem interpret_paddedFactor (f : M.Tables (Entry Param Gadget)) (v a x) :
    interpret values (paddedFactor c f v a x) =
      c.tables (fun i z y => interpret values (f i z y)) v a x := by
  by_cases h : padOK c v a x
  · rw [paddedFactor, ite_eq_left h, Network.ChannelPacking.tables]
    unfold padOK at h
    rw [ite_eq_left h]
    rfl
  · rw [paddedFactor, ite_eq_right h, Network.ChannelPacking.tables]
    unfold padOK at h
    rw [ite_eq_right h, map_zero]

end Uniform

variable {Param Gadget E : Type*} [CommSemiring E] (tags : N.Tables (Entry Param Gadget))
    (values : Gadget → E)

/-- For a whole vector of fixed private assignments the retained cell table
is one tagged local term in the actual physical, uniformly padded grid. -/
noncomputable def conditionedGridTags (hidden : ∀ i, N.InsideAssignment cell i) :
    ((N.cellNetwork cell position).uniformGrid src dst H).Tables (Entry Param Gadget) :=
  paddedFactor packing (conditionedCellTags cell position tags hidden)

/-- The packed polynomial entry at one public box sums only the hidden
assignments of that box. Other boxes' private wires need no guess here. -/
theorem gridTables_eq_local_sum (v : Cell) (a x) :
    packing.tables (N.cellTables cell position (fun i z y => interpret values (tags i z y))) v a x =
    ∑ h : N.InsideAssignment cell v, interpret values (conditionedGridTags cell position packing tags
      (Function.update (fun _ _ _ => false) v h) v a x) := by
  simp only [conditionedGridTags, interpret_paddedFactor, Network.ChannelPacking.tables]
  split
  · rw [cellTables_eq_local_sum]
    apply Finset.sum_congr rfl
    intro h _
    simp only [conditionedCellTags, Function.update_self]
  · simp

/-- Sum over the independent fine assignments of each box after fixing all
crossing words. There is one fine assignment for each such vector and boundary. -/
theorem sum_conditioned_cell_value (x : Ports bits) :
    (∑ h : ∀ i, N.InsideAssignment cell i, (N.cellNetwork cell position).value
      (fun v z y => interpret values (conditionedCellTags cell position tags h v z y)) x) =
    N.value (fun v z y => interpret values (tags v z y)) x := by
  unfold Network.value
  rw [Finset.sum_comm]
  let term (q : N.CrossingAssignment cell × (∀ i, N.InsideAssignment cell i)) :=
    ∏ v, (N.cellNetwork cell position).read
      (fun u z y => interpret values (conditionedCellTags cell position tags q.2 u z y)) q.1 x v
  trans ∑ q, term q
  · rw [Fintype.sum_prod_type]
    exact Finset.sum_congr (Finset.ext fun _ => by simp) fun _ _ => rfl
  symm
  apply Fintype.sum_equiv (N.cellAssignmentEquiv cell)
  intro a
  change (∏ v, interpret values (N.read tags a x v)) = _
  rw [← map_prod (interpret values)]
  trans interpret values (∏ c, cellEntry N cell tags ((N.cellAssignmentEquiv cell a).1)
    ((N.cellAssignmentEquiv cell a).2) x c)
  · rw [prod_cellEntry, Equiv.symm_apply_apply]
    rfl
  · rw [map_prod]
    apply Finset.prod_congr rfl
    intro c _
    exact congrArg (interpret values) (conditionedCellTags_read cell position tags _ _ x c).symm

/-- Expanding all private cell assignments gives exactly the fine polynomial
network, with every public channel read from its assigned slot and every
unused position forced to zero. -/
theorem sum_conditioned_grid_value (x : Ports bits) :
    (∑ h : ∀ i, N.InsideAssignment cell i, ((N.cellNetwork cell position).uniformGrid src dst H).value
      (fun v z y => interpret values (conditionedGridTags cell position packing tags h v z y)) x) =
    N.value (fun v z y => interpret values (tags v z y)) x := by
  simp only [conditionedGridTags, interpret_paddedFactor, Network.ChannelPacking.value_uniformGrid]
  exact sum_conditioned_cell_value cell position tags values x

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
