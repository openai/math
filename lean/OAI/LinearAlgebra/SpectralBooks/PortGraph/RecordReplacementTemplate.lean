import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementTerm
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementSmallShape

/-! # Numbered replacement templates for the terms of a patch record

Every term has the same old stub type and polarities. The direct term has
one role with the stubs numbered in boundary order. In a pruned term the
old stub names identify its output and input leaves, and the output, left,
and right positions of each branch determine its three port numbers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.PatchShape.RecordTerm

open PlanarPatch UniformDecorations ReplacementTemplate

variable {K w : ℕ} {F : Type} [Field F] {R : PatchShape K} {hc : R.InternallyConnected}

section Pruned

variable {b : ℕ} (total : Fintype.card R.Stub = b+1)
  (large : 3 ≤ b)
  (t : TrivalentTree (MvPolynomial (Address w) F) (fun _ : R.Stub => 2^w) (2^w))
  (labels : t.labels = (List.finRange b).map (fun i => (R.contourSlots hc total).symm i.castSucc))

include labels large in
/-- A large term has at least two input leaves, hence its top is a branch. -/
theorem rootMem : [] ∈ t.branchAddresses := by
  apply t.root_mem_of_two_labels
  rw [labels, List.length_map, List.length_finRange]
  omega

include labels in
/-- Moving the final contour position to the front gives exactly the tree's
output followed by its ordered input labels. -/
theorem stubNames_complete :
    let out := (R.contourSlots hc total).symm (Fin.last b)
    (out :: t.labels).Nodup ∧ ∀ s, s ∈ out :: t.labels := by
  let e := R.contourSlots hc total
  change (e.symm (Fin.last b) :: t.labels).Nodup ∧ ∀ s, s ∈ e.symm (Fin.last b) :: t.labels
  rw [labels]
  constructor
  · apply List.nodup_cons.mpr
    refine ⟨?_, (List.nodup_finRange b).map (e.symm.injective.comp (Fin.castSucc_injective b))⟩
    rintro h
    obtain ⟨i,_,hi⟩ := List.mem_map.mp h
    exact Fin.castSucc_ne_last i (e.symm.injective hi)
  · intro s
    obtain ⟨i,rfl⟩ := e.symm.surjective s
    induction i using Fin.lastCases with
    | last => exact .head _
    | cast i => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)

/-- Read the tree stub bearing the given old stub name. -/
def stubEquiv : R.Stub ≃ t.Stub :=
  (t.stubNames ((R.contourSlots hc total).symm (Fin.last b))
    (stubNames_complete total t labels).1 (stubNames_complete total t labels).2).symm

@[simp] theorem stubEquiv_symm_output :
    (stubEquiv total t labels).symm none = (R.contourSlots hc total).symm (Fin.last b) := rfl

@[simp] theorem stubEquiv_symm_input (p : t.Leaf) :
    (stubEquiv total t labels).symm (some p) = t.leafName p := rfl

include labels in
/-- The move from last output to first output is a cyclic rotation of the
stub word, hence preserves its successor permutation. -/
theorem formPerm_labels :
    ((R.contourSlots hc total).symm (Fin.last b) :: t.labels).formPerm =
      R.contourStubWord.formPerm := by
  let out := (R.contourSlots hc total).symm (Fin.last b)
  have hw : R.contourStubWord = t.labels ++ [out] := by
    rw [labels, ← List.ofFn_eq_map]
    exact R.contourStubWord_eq_prefix_append_last hc total
  rw [hw]
  simpa [List.rotate_cons_succ] using
    (List.formPerm_rotate_one (out :: t.labels) (stubNames_complete total t labels).1).symm

end Pruned

variable (u : R.RecordTerm hc w F)

/-- The actual internal graph and the attachment of each old stub. -/
def piece : OpenPiece R.Stub :=
  match u with
  | .direct _ => (singleRole (fun s : R.Stub => s.val.side)).piece
  | .pruned total large t labels _ _ _ =>
    { Vertex := t.Role, Edge := t.InternalWire, graph := t.internalGraph,
      attach := t.attach (rootMem total large t labels) ∘ stubEquiv total t labels }

/-- The root role of the replacement tree. -/
def rootRole : u.piece.Vertex :=
  match u with
  | .direct _ => ()
  | .pruned total large t labels _ _ _ => ⟨[],rootMem total large t labels⟩

/-- Rooted internal wiring selected by the term. -/
def tree : RootedTreeData u.piece.graph u.rootRole :=
  match u with
  | .direct _ => (singleRole (fun s : R.Stub => s.val.side)).tree
  | .pruned total large t labels _ _ _ => t.rootedTreeData (rootMem total large t labels)

/-- The catalogue template retains the exact same old stub type and directions
on both branches of patch replacement. -/
def template : ReplacementTemplate.{0,0,0} where
  Role := u.piece.Vertex
  Wire := u.piece.Edge
  Stub := R.Stub
  graph := u.piece.graph
  root := u.rootRole
  tree := u.tree
  attach := u.piece.attach
  direction s := s.val.side

instance : Fintype u.template.Role := u.piece.vertexFintype
instance : Fintype u.template.Wire := u.piece.edgeFintype
instance : Fintype u.template.Stub := inferInstanceAs (Fintype R.Stub)

@[simp] theorem template_direction (s : R.Stub) : u.template.direction s = s.val.side := rfl

/-- The common degree of the roles of this term. -/
def arity : ℕ :=
  match u with
  | .direct _ => Fintype.card R.Stub
  | .pruned .. => 3

theorem arity_le_three : u.arity ≤ 3 := by
  cases u with
  | direct h => exact h
  | pruned => exact le_rfl

/-- Old contour order at a direct role, and output, left, right at a tree role. -/
def slotEquiv : (v : u.template.Role) → LocalPort u.template v ≃ Fin u.arity :=
  match u with
  | .direct _ => singleNumbering (fun s : R.Stub => s.val.side) (R.contourStubEquiv hc).symm
  | .pruned total large t labels _ _ _ =>
    t.namedSlotEquiv (rootMem total large t labels) (stubEquiv total t labels)

/-- The same numbering with the cardinality convention used to assemble a map. -/
def numbering (v : u.piece.Vertex) :
    LocalPort u.template v ≃ Fin (Fintype.card (LocalPort u.template v)) :=
  (u.slotEquiv v).trans (finCongr ((Fintype.card_congr (u.slotEquiv v)).trans (Fintype.card_fin _)).symm)

/-- The consecutive numbers at a role as slots in the four-position catalogue. -/
def slot (v : u.template.Role) : LocalPort u.template v ↪ Fin 4 :=
  (u.slotEquiv v).toEmbedding.trans (Fin.castLEEmb (u.arity_le_three.trans (by decide)))

/-- A replacement term with `b` stubs has exactly `max 1 (b-2)` vertices. -/
theorem roles_eq : Fintype.card u.template.Role = max 1 (Fintype.card R.Stub - 2) := by
  cases u with
  | direct h => exact single_role_count (fun s : R.Stub => s.val.side) h
  | pruned total large t labels bound count cost =>
    change Fintype.card t.Role = _
    rw [t.card_role]
    omega

/-- A patch with no boundary stub has one role and no internal wire. -/
theorem wires_zero_of_no_stubs (h : Fintype.card R.Stub = 0) :
    Fintype.card u.piece.Edge = 0 := by
  cases u with
  | direct small => exact Fintype.card_empty
  | pruned total => omega

theorem roles_le : Fintype.card u.template.Role ≤ max 1 (Fintype.card R.Stub) := by
  rw [u.roles_eq]
  omega

end PortGraph.PatchShape.RecordTerm

end

end SpectralBooks
end LinearAlgebra
end OAI
