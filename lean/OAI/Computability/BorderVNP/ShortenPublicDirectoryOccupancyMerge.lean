import OAI.Computability.BorderVNP.ShortenPublicParallelNames

/-! # Merging the independent cable presence column

Each child occupies one public rectangle. Its presence column follows the same
permutation as its cable rows, while the existing merge translates its pointers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicParallel

open PublicSegments Crossing
open VPVNP.VerifierNetwork (Frame)

variable {B X : Type*} [Fintype B] [Fintype X] {copies V E w : ℕ}

/-- One Boolean frame for presence and the existing merged table. Presence is direct wiring. -/
noncomputable def occupiedMerge
    (merge : Frame (Fin copies × Raw B V E w w) (Raw B (copies*V) (copies*E) w w)) :
    Frame (Fin copies × (Fin E ⊕ Raw B V E w w)) (Fin (copies*E) ⊕ Raw B (copies*V) (copies*E) w w) :=
  let child : Frame (Fin copies × (Fin E ⊕ Raw B V E w w)) (Fin copies × Raw B V E w w) :=
    Frame.initial fun z => (z.1,.inr z.2)
  (merge.subst child).withInput.select (Sum.elim (fun j =>
    let z := finProdFinEquiv.symm j
    Sum.inl (z.1,Sum.inl z.2)) Sum.inr)

/-- The merged table uses no extra gates for the presence column. -/
theorem occupiedMerge_size
    (merge : Frame (Fin copies × Raw B V E w w) (Raw B (copies*V) (copies*E) w w)) :
    (occupiedMerge merge).size = merge.size := by
  simp [occupiedMerge]

variable (merge : Frame (Fin copies × Raw B V E w w) (Raw B (copies*V) (copies*E) w w))
variable (x : Fin copies × (Fin E ⊕ Raw B V E w w) → Bool)

/-- The merged segment table is precisely the ordinary merger applied to the child tables. -/
theorem occupiedMerge_raw :
    (occupiedMerge merge).eval x ∘ Sum.inr = merge.eval (fun z => x (z.1,.inr z.2)) := by
  funext j
  simp only [Function.comp_apply,occupiedMerge,Frame.select_eval,Sum.elim_inr,Frame.withInput_eval_inr,Frame.subst_eval]
  apply congrArg (fun t => merge.eval t j)
  funext z
  exact Frame.initial_eval _ _ _

/-- Reading the presence column at a flat row reads the corresponding child bit. -/
theorem occupiedMerge_flag (i : Fin copies) (r : Fin E) :
    (occupiedMerge merge).eval x (.inl (flat i r)) = x (i,.inl r) := by
  simp only [occupiedMerge,Frame.select_eval,Sum.elim_inl,unflat_flat,Frame.withInput_eval_inl]

/-- The global presence bit holds exactly on the stable names of the parallel layout. -/
theorem occupiedMerge_occupied {Edge : Fin copies → Type*} (rows : ∀ i, Edge i ↪ Fin E)
    (present : ∀ i r, x (i,.inl r) = true ↔ r ∈ Set.range (rows i))
    (j : Fin (copies*E)) :
    (occupiedMerge merge).eval x (.inl j) = true ↔ j ∈ Set.range (parallelName rows) := by
  obtain ⟨⟨i,r⟩,rfl⟩ := finProdFinEquiv.surjective j
  rw [show finProdFinEquiv (i,r) = flat i r from rfl,occupiedMerge_flag,present,parallelName_mem]

/-- Build every occupied child once before applying the merged directory reader.
The budget includes the shared pointer-offset circuit and no additional occupancy gates. -/
theorem occupied_children_frames (child : Fin copies → Frame X (Fin E ⊕ Raw B V E w w)) :
    ∃ (g : Frame (Fin copies × Raw B V E w w) (Raw B (copies*V) (copies*E) w w))
      (out : Frame X (Fin (copies*E) ⊕ Raw B (copies*V) (copies*E) w w)),
      MergeRows g ∧ out.size ≤ 2 + (∑ i, (child i).size) + copies*E*600*(w+1)^2 ∧
      ∀ y, out.eval y = (occupiedMerge g).eval (fun z => (child z.1).eval y z.2) := by
  obtain ⟨g,hg,hr⟩ := merge_frames B copies V E w
  obtain ⟨f,hf,he⟩ := exists_parallelFrames child
  let bank := f.select (fun j : Fin copies × (Fin E ⊕ Raw B V E w w) => ⟨j.1,j.2⟩)
  refine ⟨g,(occupiedMerge g).subst bank,hr,?_,?_⟩
  · simp only [Frame.subst_size,occupiedMerge_size,bank,Frame.select_size]
    omega
  · intro y
    have hbank : bank.eval y = fun z => (child z.1).eval y z.2 := by
      funext z
      simp only [bank,Frame.select_eval,he]
    funext j
    rw [Frame.subst_eval,hbank]

end Shortening.PublicParallel

end BorderVNP
end Computability
end OAI
