import OAI.Computability.BorderVNP.ShortenPublicEndpointCharge
import OAI.Computability.BorderVNP.ShortenPublicSegmentJoin

/-! # Wiring a complete successor table into the next segment classifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicEndpoints.Successor

open Crossing StaticRows CombiningStep VPVNP.VerifierNetwork

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {A : Type} [Fintype A] (B : Type*) [Fintype B]
variable (nSites nEdges w : ℕ) {nSeeds : ℕ} (seed : A ≃ Fin nSeeds)
variable (f : Frame (Source e B A nSites nEdges nSeeds w) (Next B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w))

/-- Select the designated charge and the complete public cable/site table in the exact
input order used by the next epoch's geometric classifier. -/
noncomputable def segmentInput : Frame (Source e B A nSites nEdges nSeeds w)
    (PublicSegments.Raw B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w w) :=
  (withCharges e B nSites nEdges w seed f).select (Sum.elim Sum.inr (Sum.inl ∘ Sum.inl))

/-- The reader costs at most three additional gates per public cable candidate. -/
theorem segmentInput_size : (segmentInput e B nSites nEdges w seed f).size ≤ f.size + 3*edgeCapacity e nEdges nSeeds := by
  rw [segmentInput,Frame.select_size]
  exact withCharges_size e B nSites nEdges w seed f

variable (x : Source e B A nSites nEdges nSeeds w → Bool)

/-- Both the full site payload and the sparse cable fields pass through the selection. -/
theorem segmentInput_table (i : Inputs B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w w) :
    (segmentInput e B nSites nEdges w seed f).eval x (.inr i) = f.eval x (.inl i) :=
  (Frame.select_eval ..).trans (withCharges_table e B nSites nEdges w seed f x (.inl i))

variable [NeZero D] {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
variable (oldSite : p.layout.Site ↪ Fin nSites) (old : p.layout.Edge ↪ Fin nEdges)
variable (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A) (first : Fin D × Bool) (q : Counts e p bin perm)
variable (src : SourceData e p bin perm positive oldSite old seed dummy first q x)
variable (out : Result e p bin perm positive oldSite old seed dummy first q x (f.eval x))

include out in
/-- The actual successor pointers and widths satisfy the next endpoint join's representation predicate. -/
theorem segmentInput_rows :
    PublicEndpoints.Represents (output e p bin perm positive first q).layout (siteRows e p oldSite seed.toEmbedding)
      (outputRows e p bin perm positive first q old seed.toEmbedding) dummy
      ((segmentInput e B nSites nEdges w seed f).eval x ∘ Sum.inr) := by
  have fields : (segmentInput e B nSites nEdges w seed f).eval x ∘ Sum.inr = f.eval x ∘ Sum.inl :=
    funext (segmentInput_table e B nSites nEdges w seed f x)
  rw [fields]
  exact out.rows

include out in
/-- A public successor site carries exactly the payload supplied by the preceding site circuit. -/
theorem segmentInput_site (s : Fin (siteCapacity e nSites nSeeds)) (j : B) :
    (segmentInput e B nSites nEdges w seed f).eval x (.inr (.inl (s,j))) = x (.inl (s,j)) :=
  (segmentInput_table e B nSites nEdges w seed f x _).trans (out.sites _)

include src out in
/-- The geometric classifier receives the actual post-mask at every occupied cable name. -/
theorem segmentInput_charge (z : EdgeShape e p bin perm) :
    (segmentInput e B nSites nEdges w seed f).eval x (.inl (edgeRows e p bin perm old seed.toEmbedding z)) =
      postMask p bin perm e positive q z :=
  (Frame.select_eval ..).trans (withCharges_edge e B nSites nEdges w seed f x p bin perm positive oldSite old dummy first q src out z)

include out in
/-- Unused physical row numbers arrive at the geometric classifier with a false charge. -/
theorem segmentInput_hole (i : Fin (edgeCapacity e nEdges nSeeds)) (hi : i ∉ Set.range (edgeRows e p bin perm old seed.toEmbedding)) :
    (segmentInput e B nSites nEdges w seed f).eval x (.inl i) = false :=
  (Frame.select_eval ..).trans (withCharges_hole e B nSites nEdges w seed f x p bin perm positive oldSite old dummy first q out i hi)

end Shortening.PublicEndpoints.Successor

end BorderVNP
end Computability
end OAI
