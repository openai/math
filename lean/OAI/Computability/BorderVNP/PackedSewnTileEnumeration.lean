import OAI.Computability.BorderVNP.PackedSewnTileFragments

/-! # Grouping the physical six-slot tile directory by attached port and copy -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment.Tile

open Crossing Inherited Diagonal.ExternalSew.GridHosts
open scoped Classical

/-- Grouping the physical row directory by original grouped port and copy permutes
the rows. Each of the six slots keeps the ordinal of its actual team and tile. -/
theorem ordinal_grouped_perm {R groups copies : ℕ} (V : ℕ) (count : groups*copies = R+1) :
    (List.finRange (6*(R+1)*V)).Perm
      ((Finset.univ.toList : List (Fin groups × Fin V)).flatMap fun p =>
        (Finset.univ.toList : List (Fin copies)).flatMap fun i =>
          (List.finRange 6).map fun j => ordinal R V ((teamBlocks groups copies count).symm (p.1,i),p.2,j)) := by
  apply List.Subperm.perm_of_length_le
  · apply (List.nodup_finRange _).subperm
    intro q _
    obtain ⟨⟨u,v,j⟩,rfl⟩ := (ordinal R V).surjective q
    let z := teamBlocks groups copies count u
    apply List.mem_flatMap.mpr
    refine ⟨(z.1,v),by simp,List.mem_flatMap.mpr ⟨z.2,by simp,?_⟩⟩
    exact List.mem_map.mpr ⟨j,List.mem_finRange j,by simp [z]⟩
  · simp [List.length_flatMap,List.map_const']
    rw [← count]
    exact le_of_eq (by ring)

/-- Filtering a global port directory by the original host gives precisely that
host's attached-port directory, with each port retaining its original name. -/
theorem attached_port_perm {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (v : N.Site) :
    ((Finset.univ.toList : List P).filter fun p => decide (N.attach p = v)).Perm
      ((Finset.univ.toList : List (Attached N v)).map Subtype.val) := by
  apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _)
    ((Finset.nodup_toList _).map Subtype.val_injective)).mpr
  intro p
  simp [Attached]

/-- Reindex a guarded pass over all original ports by the attached-port subtype.
The emitted rows may depend on the proof that a port belongs to the chosen host. -/
theorem grouped_attached_flatMap_perm {D : ℕ} {P α : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (v : N.Site) (emit : Attached N v → List α) :
    ((Finset.univ.toList : List P).flatMap fun p =>
      if h : N.attach p = v then emit ⟨p,h⟩ else []).Perm
      ((Finset.univ.toList : List (Attached N v)).flatMap emit) := by
  let f (p : P) := if h : N.attach p = v then emit ⟨p,h⟩ else []
  have skip (l : List P) : l.flatMap f = (l.filter fun p => decide (N.attach p = v)).flatMap f := by
    induction l with
    | nil => rfl
    | cons a as ih => by_cases h : N.attach a = v <;> simp [f,h,ih]
  change (Finset.univ.toList.flatMap f).Perm _
  rw [skip]
  have reindex := (attached_port_perm N v).flatMap_right f
  rw [List.flatMap_map] at reindex
  have onPort (a : Attached N v) : f a.val = emit a := by simp only [f,dite_eq_left a.property]
  simpa only [Function.comp_apply,onPort] using reindex

/-- Reading the physical six-slot rows through an owner-selecting partial decoder gives
the complete attached-port and copy roster, including all multiplicities. -/
theorem selected_slot_image {D R V groups copies : ℕ} {α : Type*} {bits : Fin groups × Fin V → ℕ}
    (count : groups*copies = R+1) (N : Network D (Fin groups × Fin V) bits) (v : N.Site)
    (read : Fin (6*(R+1)*V) → Option α) (emit : Attached N v → Fin copies → List α)
    (each : ∀ (p : Fin groups × Fin V) (i : Fin copies),
      (List.finRange 6).filterMap (fun j => read (ordinal R V ((teamBlocks groups copies count).symm
        (p.1,i),p.2,j))) = if h : N.attach p = v then emit ⟨p,h⟩ i else []) :
    ((List.finRange (6*(R+1)*V)).filterMap read).Perm
      ((Finset.univ.toList : List (Attached N v)).flatMap fun a =>
        (Finset.univ.toList : List (Fin copies)).flatMap (emit a)) := by
  have perm := (ordinal_grouped_perm V count).filterMap read
  simp only [List.filterMap_flatMap,List.filterMap_map,Function.comp_def,each] at perm
  apply perm.trans
  let chunks (a : Attached N v) := (Finset.univ.toList : List (Fin copies)).flatMap (emit a)
  have guard (p : Fin groups × Fin V) :
      ((Finset.univ.toList : List (Fin copies)).flatMap fun i =>
        if h : N.attach p = v then emit ⟨p,h⟩ i else []) =
        if h : N.attach p = v then chunks ⟨p,h⟩ else [] := by
    by_cases h : N.attach p = v <;> simp [h,chunks]
  simp only [guard]
  exact grouped_attached_flatMap_perm N v chunks

end Packing.SewnField.Fragment.Tile

end BorderVNP
end Computability
end OAI
