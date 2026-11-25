import OAI.Computability.BorderVNP.PackedCableTriples
import OAI.Computability.BorderVNP.CubeMeanPhysicalTables

/-! # Cable triples on the final adaptive network

Each surviving nonlocal cable uses the physical ordinal of its edge in the
public sparse layout. Every other slot is exactly the zero triple, including
same-cell edges and unoccupied ordinals. Cell numbers in these tables are the
public ordinals consumed by the native cube chooser.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CableTriples

open Crossing CellAddressCircuit CellAddressPhysical Cube.LabelIndex Function
open private srcKey dstKey from OAI.Computability.BorderVNP.PackedCellAddressPhysical
open scoped Classical

variable {D s m n C d k w : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ) {x : σ → Bool}

/-- The embedding keeps each surviving cable in the original physical edge order. -/
def wireOrd : N.CrossingEdge cell ↪ Fin m := (Embedding.subtype _).trans edgeID

/-- All three words for an occupied sparse slot on the actual network. -/
theorem row_edge (h : Represents N cell aux siteID edgeID portID F x)
    (code : ∀ c, (F.cells c).val = c.val) (e : N.Edge) :
    row F x (edgeID e) = if cell (N.src e) = cell (N.dst e) ∨ N.width e = 0 then ⟨0,0,0⟩
      else ⟨(cell (N.src e)).val,(cell (N.dst e)).val,N.width e⟩ := by
  have he : (data F x).edge (edgeID e) = N.width e := h.edge e
  simp only [row,srcKey N cell aux siteID edgeID portID F h,dstKey N cell aux siteID edgeID portID F h,
    he,code,Fin.val_inj]

/-- A positive-width crossing row supplies the true endpoints and compressed width. -/
theorem row_crossing (h : Represents N cell aux siteID edgeID portID F x)
    (code : ∀ c, (F.cells c).val = c.val) (e : N.CrossingEdge cell) :
    row F x (wireOrd N cell edgeID e) = if N.width e.val = 0 then ⟨0,0,0⟩
      else ⟨(cell (N.src e.val)).val,(cell (N.dst e.val)).val,N.width e.val⟩ := by
  simpa only [wireOrd,Embedding.trans_apply,Embedding.subtype_apply,e.property,false_or] using
    row_edge N cell aux siteID edgeID portID F h code e.val

/-- Vacant slots have zero width irrespective of the unresolved site pointer. -/
theorem row_hole (h : Represents N cell aux siteID edgeID portID F x)
    (i : Fin m) (hi : i ∉ Set.range edgeID) : row F x i = ⟨0,0,0⟩ := by
  exact ite_eq_left (Or.inr (h.edgeHole i hi))

/-- Every slot outside the crossing-edge embedding has three zero words. -/
theorem row_unused (h : Represents N cell aux siteID edgeID portID F x)
    (code : ∀ c, (F.cells c).val = c.val) (i : Fin m) (hi : i ∉ Set.range (wireOrd N cell edgeID)) :
    row F x i = ⟨0,0,0⟩ := by
  by_cases occupied : i ∈ Set.range edgeID
  · obtain ⟨e,rfl⟩ := occupied
    have same : cell (N.src e) = cell (N.dst e) := by
      by_contra ne
      exact hi ⟨⟨e,ne⟩,rfl⟩
    rw [row_edge N cell aux siteID edgeID portID F h code,ite_eq_left (Or.inl same)]
  · exact row_hole N cell aux siteID edgeID portID F h i occupied

/-- Every sparse cable row names legal cells, including the zero sentinel. -/
theorem row_endpoints (h : Represents N cell aux siteID edgeID portID F x)
    (code : ∀ c, (F.cells c).val = c.val) (pos : 0 < C) (i : Fin m) :
    (row F x i).src < C ∧ (row F x i).dst < C := by
  by_cases occupied : i ∈ Set.range edgeID
  · obtain ⟨e,rfl⟩ := occupied
    rw [row_edge N cell aux siteID edgeID portID F h code]
    split
    · exact ⟨pos,pos⟩
    · exact ⟨(cell _).isLt,(cell _).isLt⟩
  · rw [row_hole N cell aux siteID edgeID portID F h i occupied]
    exact ⟨pos,pos⟩

end Packing.CableTriples

end BorderVNP
end Computability
end OAI
