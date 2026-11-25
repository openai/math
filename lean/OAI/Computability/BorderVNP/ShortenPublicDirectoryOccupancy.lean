import OAI.Computability.BorderVNP.ShortenPublicEndpointSegmentInput

/-! # Physical occupancy alongside the successor segment table

A live interval can have width zero and a retained cable can have its charge cleared.
The old-cable directory therefore needs the successor serializer's separate occupancy bit.
The same charge computation supplies both this directory and the geometric classifier.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicEndpoints.Successor

open Crossing StaticRows CombiningStep VPVNP.VerifierNetwork

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {A : Type} [Fintype A] (B : Type*) [Fintype B]
variable (nSites nEdges w : ℕ) {nSeeds : ℕ} (seed : A ≃ Fin nSeeds)
variable (f : Frame (Source e B A nSites nEdges nSeeds w)
  (Next B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w))

/-- The geometric segment table together with one independent presence bit per public cable. -/
noncomputable def occupiedSegmentInput : Frame (Source e B A nSites nEdges nSeeds w)
    (Fin (edgeCapacity e nEdges nSeeds) ⊕
      PublicSegments.Raw B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w w) :=
  (withCharges e B nSites nEdges w seed f).select
    (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.elim Sum.inr (Sum.inl ∘ Sum.inl)))

/-- Keeping the occupancy wires uses the same gates as producing the segment table alone. -/
theorem occupiedSegmentInput_size :
    (occupiedSegmentInput e B nSites nEdges w seed f).size =
      (segmentInput e B nSites nEdges w seed f).size := by
  simp only [occupiedSegmentInput,segmentInput,Frame.select_size]

variable (x : Source e B A nSites nEdges nSeeds w → Bool)

/-- Dropping the presence wires recovers the existing next-epoch reader on every input. -/
theorem occupiedSegmentInput_raw :
    (occupiedSegmentInput e B nSites nEdges w seed f).eval x ∘ Sum.inr =
      (segmentInput e B nSites nEdges w seed f).eval x := by
  funext j
  simp only [Function.comp_apply,occupiedSegmentInput,segmentInput,Frame.select_eval,Sum.elim_inr]

/-- The presence wire is the exact output of the successor serializer. -/
theorem occupiedSegmentInput_flag (i : Fin (edgeCapacity e nEdges nSeeds)) :
    (occupiedSegmentInput e B nSites nEdges w seed f).eval x (.inl i) = f.eval x (.inr i) :=
  (Frame.select_eval ..).trans (withCharges_table e B nSites nEdges w seed f x (.inr i))

variable [NeZero D] {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
variable (positive : p.layout.Edge → Bool) (oldSite : p.layout.Site ↪ Fin nSites)
variable (old : p.layout.Edge ↪ Fin nEdges)
variable (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A)
variable (first : Fin D × Bool) (q : Counts e p bin perm)

/-- Presence is equivalent to having a cable in the actual sewn layout, for all widths. -/
theorem occupiedSegmentInput_occupied
    (out : Result e p bin perm positive oldSite old seed dummy first q x (f.eval x))
    (i : Fin (edgeCapacity e nEdges nSeeds)) :
    (occupiedSegmentInput e B nSites nEdges w seed f).eval x (.inl i) = true ↔
      i ∈ Set.range (outputRows e p bin perm positive first q old seed.toEmbedding) := by
  rw [occupiedSegmentInput_flag]
  exact out.occupied i

end Shortening.PublicEndpoints.Successor

end BorderVNP
end Computability
end OAI
