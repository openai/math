import OAI.Computability.BorderVNP.PackedInheritedPlacementTies
import OAI.Computability.BorderVNP.PackedSubdivision

/-! # Exact incidence intervals at a retained site of a wire subdivision

A former source reads hop zero; a destination reads the last hop. When a
subdivided loop returns to its source, the old table's single word comes from
hop zero. Equality relays test all adjacent hops separately. Exterior ports
keep their original attachments. One whole-word interval per nonempty input
binds the old sparse tape to the corresponding new physical lanes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing Placement
open scoped Classical

variable {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (route : N.WireRoutes) (v : N.Site)
local notation "G" => N.subdivide route

/-- Source-first endpoint choice of the subdivided local table, including self-loops. -/
noncomputable def endpoint (e : Incident N v) : Incident G (.inl v) :=
  if h : N.src e.val = v then ⟨⟨e.val,0⟩,Or.inl (congrArg Sum.inl h)⟩
  else ⟨⟨e.val,Fin.last _⟩,Or.inr (by simp [Network.subdivide,e.property.resolve_left h])⟩

omit [Fintype P] in
/-- The subdivided table always reads a word of exactly the old width. -/
@[simp] theorem endpoint_width (e : Incident N v) : (G).width (endpoint N route v e).val = N.width e.val := by
  unfold endpoint
  split <;> rfl

/-- An exterior port keeps its old name and attaches to the retained source site. -/
def attached (p : Attached N v) : Attached G (.inl v) := ⟨p.val,congrArg Sum.inl p.property⟩

/-- The actual new incident word used by the prior site table. -/
noncomputable def nextRow : Row N v → Row G (.inl v) :=
  Sum.map (endpoint N route v) (attached N route v)

variable (oldID : N.Edge ↪ Fin m) (newID : (N.subdivide route).Edge ↪ Fin n) (portID : P ↪ Fin np)

/-- One physical copy from a chosen endpoint word into its old site-local input slot. -/
noncomputable def slice (r : Row N v) : Slice :=
  ⟨localStart N oldID portID v r,localStart G newID portID (.inl v) (nextRow N route v r),width N v r⟩

/-- The public rows are emitted in source ID order. Empty old words consume no records. -/
noncomputable def cuts : List Slice :=
  ((ordered N oldID portID v).filter fun r => decide (0 < width N v r)).map (slice N route v oldID newID portID)

/-- The location of each old input bit in the newly presented incidence array. -/
noncomputable def nextLane : InputLane N v → InputLane G (.inl v)
  | .inl ⟨e,j⟩ => .inl ⟨endpoint N route v e,Fin.cast (endpoint_width N route v e).symm j⟩
  | .inr ⟨p,j⟩ => .inr ⟨attached N route v p,j⟩

/-- Project the subdivided incidence vector onto the old source-first table input. -/
noncomputable def read : Fin (incoming N v) → Fin (incoming G (.inl v)) :=
  sourceOrder G newID portID (.inl v) ∘ nextLane N route v ∘ (sourceOrder N oldID portID v).symm

private theorem limits (r : Row N v) :
    (slice N route v oldID newID portID r).oldStart+width N v r ≤ incoming N v ∧
    (slice N route v oldID newID portID r).newStart+width N v r ≤ incoming G (.inl v) := by
  cases r with
  | inl e =>
    refine ⟨wireEnd_le N oldID portID v e,?_⟩
    change wireStart G newID portID (.inl v) (endpoint N route v e) + N.width e.val ≤ _
    rw [←endpoint_width N route v e]
    exact wireEnd_le G newID portID (.inl v) (endpoint N route v e)
  | inr p =>
    exact ⟨portEnd_le N oldID portID v p,portEnd_le G newID portID (.inl v) (attached N route v p)⟩

private theorem lane (r : Row N v) (j : Fin (width N v r)) :
    ∃ k : Fin (incoming N v), k.val = (slice N route v oldID newID portID r).oldStart+j.val ∧
      (read N route v oldID newID portID k).val = (slice N route v oldID newID portID r).newStart+j.val := by
  cases r with
  | inl e =>
    refine ⟨sourceOrder N oldID portID v (.inl ⟨e,j⟩),wireOrdinal N oldID portID v e j,?_⟩
    simp only [read,Function.comp_apply,Equiv.symm_apply_apply,nextLane]
    exact wireOrdinal G newID portID (.inl v) (endpoint N route v e) _
  | inr p =>
    refine ⟨sourceOrder N oldID portID v (.inr ⟨p,j⟩),portOrdinal N oldID portID v p j,?_⟩
    simp only [read,Function.comp_apply,Equiv.symm_apply_apply,nextLane]
    exact portOrdinal G newID portID (.inl v) (attached N route v p) j

private theorem has_cut (r : Row N v) (positive : 0 < width N v r) :
    slice N route v oldID newID portID r ∈ cuts N route v oldID newID portID := by
  apply List.mem_map.mpr ⟨r,?_,rfl⟩
  apply List.mem_filter.mpr
  exact ⟨by simp [ordered],decide_eq_true positive⟩

/-- The sparse whole-word rows cover exactly the canonical reading of every old bit. -/
theorem covers : Covers (incoming N v) (incoming G (.inl v)) (cuts N route v oldID newID portID)
    (read N route v oldID newID portID) := by
  refine { oldFit := ?old, newFit := ?new, agrees := ?agrees, covers := ?covers }
  case old =>
    rintro p hp
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
    exact (limits N route v oldID newID portID r).1
  case new =>
    rintro p hp
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
    exact (limits N route v oldID newID portID r).2
  case agrees =>
    rintro p hp
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
    intro j
    obtain ⟨k,ho,hn⟩ := lane N route v oldID newID portID r j
    exact (congrArg (fun t => (read N route v oldID newID portID t).val) (Fin.ext ho).symm).trans hn
  case covers =>
    intro k
    obtain ⟨a,rfl⟩ := (sourceOrder N oldID portID v).surjective k
    rcases a with ⟨e,j⟩ | ⟨p,j⟩
    · exact ⟨_,has_cut N route v oldID newID portID (.inl e) (Nat.zero_lt_of_lt j.isLt),j,
        (wireOrdinal N oldID portID v e j).symm⟩
    · exact ⟨_,has_cut N route v oldID newID portID (.inr p) (Nat.zero_lt_of_lt j.isLt),j,
        (portOrdinal N oldID portID v p j).symm⟩

/-- One record per nonempty old incidence, independent of each represented word's width. -/
theorem cuts_count : (cuts N route v oldID newID portID).length ≤
    Fintype.card (Incident N v)+Fintype.card (Attached N v) := by
  simp only [cuts,List.length_map]
  exact (List.length_filter_le ..).trans_eq (by simp [ordered,Row])

end Packing.Inherited.Subdivision

end BorderVNP
end Computability
end OAI
