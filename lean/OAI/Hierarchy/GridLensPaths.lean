import OAI.Hierarchy.GridLens

namespace OAI
/-! # Packing paths into a finite collection of geometric segments -/

namespace Hierarchy.GridLens
open scoped BigOperators

variable {A T M : Type*}

/-- Endpoints of the two legs of a path, separated by the waypoint `via`. -/
def legSite (ends : A → Bool → M) (via : A → M) (i : A × Bool) (side : Bool) : M :=
  if i.2 then (if side then ends i.1 true else via i.1)
  else (if side then via i.1 else ends i.1 false)

/-- A path can traverse its segment in either direction. Empty legs are stationary.
Distinct nonempty legs use distinct physical segments. -/
structure SegmentPaths (ends : A → Bool → M) (segment : T → Bool → M) where
  via : A → M
  claim : A × Bool → Option T
  disjoint : ∀ {i i' t}, claim i = some t → claim i' = some t → i = i'
  attachments : ∀ i, match claim i with
    | none => legSite ends via i false = legSite ends via i true
    | some t => (legSite ends via i false = segment t false ∧ legSite ends via i true = segment t true) ∨
        (legSite ends via i false = segment t true ∧ legSite ends via i true = segment t false)

private theorem sum_claim_le {I : Type*} [Fintype I] [Fintype T] (claim : I → Option T)
    (cost : T → ℝ) (nn : ∀ t, 0 ≤ cost t)
    (disjoint : ∀ {i i' t}, claim i = some t → claim i' = some t → i = i') :
    (∑ i, (claim i).elim 0 cost) ≤ ∑ t, cost t := by
  classical
  calc
    _ = ∑ i, ∑ t, (if claim i = some t then cost t else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : claim i with
      | none => simp
      | some t => simp
    _ = ∑ t, ∑ i, (if claim i = some t then cost t else 0) := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t _
      let fiber := Finset.univ.filter (fun i => claim i = some t)
      have hcard : fiber.card ≤ 1 := Finset.card_le_one.mpr fun i hi i' hi' =>
        disjoint (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2
      have realcard : (fiber.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      simpa [Finset.sum_ite, nsmul_eq_mul, fiber] using
        (mul_le_mul_of_nonneg_right realcard (nn t))

/-- Geometric distances of the demands are bounded by the sum of available segment lengths.
The witness consists entirely of point identifications and an injective assignment of segments. -/
theorem SegmentPaths.sum_dist_le [Fintype A] [Fintype T] [PseudoMetricSpace M]
    {ends : A → Bool → M} {segment : T → Bool → M} (p : SegmentPaths ends segment) :
    (∑ a, dist (ends a false) (ends a true)) ≤ ∑ t, dist (segment t false) (segment t true) := by
  let cost := fun t => dist (segment t false) (segment t true)
  let leg := fun i => dist (legSite ends p.via i false) (legSite ends p.via i true)
  have length_eq (i : A × Bool) : leg i = (p.claim i).elim 0 cost := by
    have h := p.attachments i
    cases e : p.claim i with
    | none =>
      rw [e] at h
      simp [leg, h]
    | some t =>
      rw [e] at h
      rcases h with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;> simp [leg, cost, h₀, h₁, dist_comm]
  calc
    _ ≤ ∑ a, (leg (a,true) + leg (a,false)) := by
      apply Finset.sum_le_sum
      intro a _
      simpa [leg, legSite, add_comm] using dist_triangle (ends a false) (p.via a) (ends a true)
    _ = ∑ i : A × Bool, leg i := by simp [Fintype.sum_prod_type]
    _ = ∑ i, (p.claim i).elim 0 cost := Finset.sum_congr rfl fun i _ => length_eq i
    _ ≤ _ := sum_claim_le p.claim cost (fun _ => dist_nonneg) p.disjoint

end Hierarchy.GridLens

end OAI
