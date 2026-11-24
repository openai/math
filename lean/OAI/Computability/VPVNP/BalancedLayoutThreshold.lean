import OAI.Computability.VPVNP.BalancedWireLayout
import OAI.Computability.VPVNP.SpectralInterpolation
import Mathlib.Order.CountableDenseLinearOrder

/-!
# A common strict threshold for balanced cube layouts

Theorem 4.2 compares a single star witness with every balanced cut. The
extension places all subset centroids simultaneously. Its terminal wire lengths
and its bridge length can therefore be computed in one filled cube. Finiteness
of the cuts makes the strict savings uniform before the tensor is chosen.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

/-- Choose one positive saving below the unit-cube star length for every
balanced split of the same dimension, including at the dimension threshold. -/
theorem balancedCut_uniformGap {n : ℕ} {C : ℝ} (hC : 1 ≤ C) (hdim : 18 * C^2 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : Finset (Fin n), n ≤ 3*s.card → 3*s.card ≤ 2*n →
      C * √((s.card : ℝ)⁻¹ + (sᶜ.card : ℝ)⁻¹) + (starLength s.card + starLength sᶜ.card) <
        starLength n - ε := by
  classical
  let cuts := Finset.univ.filter (fun s : Finset (Fin n) ↦ n ≤ 3*s.card ∧ 3*s.card ≤ 2*n)
  let cost (s : Finset (Fin n)) :=
    C * √((s.card : ℝ)⁻¹ + (sᶜ.card : ℝ)⁻¹) + (starLength s.card + starLength sᶜ.card)
  have hcost {s} (hs : s ∈ cuts) : cost s < starLength n := by
    obtain ⟨hlo, hhi⟩ := (Finset.mem_filter.mp hs).2
    have h := balancedLayout_strict hC hdim s hlo hhi (basisCentroid n)
    rw [subsetCentroid_star_length, subsetCentroid_star_length,
      disjoint_subsetCentroids_dist disjoint_compl_right, basisCentroid_star_length] at h
    simpa only [cost, starLength, add_comm (C * _) (_ + _)] using h
  obtain ⟨t, hbelow, habove⟩ := Order.exists_between_finsets (cuts.image cost) {starLength n} (by
    rintro _ hx y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_singleton.mp hy]
    exact hcost hs)
  refine ⟨starLength n - t, sub_pos.mpr (habove _ (Finset.mem_singleton_self _)), ?_⟩
  intro s hlo hhi
  rw [sub_sub_cancel]
  exact hbelow _ (Finset.mem_image_of_mem cost (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo, hhi⟩))

end SpectralGeometry

namespace WireTensor.SpectralPoint

open SpectralGeometry
open scoped symmDiff

variable {k J : Type*} [Field k] [Fintype J]

/-- The bridge and the sum of terminal distances in a spectral realization of
the two filled side centroids. The boolean side convention agrees with the
two-center circuit factorization. -/
theorem centroid_wire_costs (F : SpectralPoint k J) {n : ℕ} (corner : Finset (Fin n) → J)
    (c : Finset (Fin n) → J) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcorner : ∀ A B, F.wireDistance (corner A) (corner B)^2 = σ^2 * (A ∆ B).card)
    {X : Type*} [MetricSpace X] (hc : HasCATZeroSegments X) (e : J → X)
    (he : ∀ a b, dist (e a) (e b) = F.wireDistance a b)
    (hcentroid : ∀ s, e (c s) = filledSubsetCentroid hc (e ∘ corner) s)
    (s : Finset (Fin n)) :
    F.wireDistance (c s) (c sᶜ) = σ * √((s.card : ℝ)⁻¹ + (sᶜ.card : ℝ)⁻¹) ∧
      (∑ i, F.wireDistance (corner {i}) (if cutSide s i then c sᶜ else c s)) =
        σ * (starLength s.card + starLength sᶜ.card) := by
  have hf (A B) : dist ((e ∘ corner) A) ((e ∘ corner) B)^2 = σ^2 * (A ∆ B).card := by
    rw [Function.comp_apply, Function.comp_apply, he, hcorner]
  have hsum (t : Finset (Fin n)) :
      (∑ i ∈ t, F.wireDistance (corner {i}) (c t)) = σ * starLength t.card := by
    simpa only [← he, hcentroid, Function.comp_apply, starLength] using
      filledSubsetCentroid_star_length hc (e ∘ corner) hσ hf t
  constructor
  · rw [← he, hcentroid, hcentroid]
    exact disjoint_filledSubsetCentroids_dist hc (e ∘ corner) hσ hf disjoint_compl_right
  · rw [← s.sum_add_sum_compl, mul_add, ← hsum, ← hsum]
    congr 1
    · exact Finset.sum_congr rfl fun i hi ↦ by simp [cutSide, hi]
    · exact Finset.sum_congr rfl fun i hi ↦ by simp [cutSide, Finset.mem_compl.mp hi]

variable {J : Type} [Fintype J]

/-- Extend the marked cube to one spectrum with two centers for each cut, then
choose a threshold strictly between all balanced layouts and the star bound.
The same margin can be used to select the tensor witness in (4.4). -/
theorem exists_cubeCentroid_layout_threshold (F : SpectralPoint k J) {n : ℕ}
    (corner : Finset (Fin n) → J) {σ C : ℝ} (hσ : 0 < σ)
    (hcorner : ∀ A B, F.wireDistance (corner A) (corner B)^2 = σ^2 * (A ∆ B).card)
    (hC : 1 ≤ C) (hdim : 18 * C^2 ≤ n)
    (embedding : ∀ S : ExtendedSpectrum F, ∃ (X : Type) (_ : MetricSpace X)
      (_ : HasCATZeroSegments X) (e : S.Parties → X),
      ∀ a b, dist (e a) (e b) = S.point.wireDistance a b) :
    ∃ (S : ExtendedSpectrum F) (centers : Finset (Fin n) → Bool → S.Parties) (ε : ℝ),
      0 < ε ∧ ∀ s : Finset (Fin n), n ≤ 3*s.card → 3*s.card ≤ 2*n →
        C * S.point.wireDistance (centers s false) (centers s true) +
          ∑ i, S.point.wireDistance (S.old (corner {i})) (centers s (cutSide s i)) <
          σ * (starLength n - ε) := by
  obtain ⟨S, c, hcentroid⟩ := F.exists_cubeCentroid_extension corner
  obtain ⟨X, hX, hc, e, he⟩ := embedding S
  obtain ⟨ε, hε, hgap⟩ := balancedCut_uniformGap hC hdim
  refine ⟨S, fun s b ↦ if b then c sᶜ else c s, ε, hε, fun s hlo hhi ↦ ?_⟩
  have hcube (A B) : S.point.wireDistance ((S.old ∘ corner) A) ((S.old ∘ corner) B)^2 =
      σ^2 * (A ∆ B).card := by
    rw [Function.comp_apply, Function.comp_apply, S.distances, hcorner]
  obtain ⟨bridge, outer⟩ := S.point.centroid_wire_costs (S.old ∘ corner) c hσ.le hcube hc e he
    (hcentroid X hc e he) s
  change C * S.point.wireDistance (c s) (c sᶜ) +
    (∑ i, S.point.wireDistance ((S.old ∘ corner) {i}) (if cutSide s i then c sᶜ else c s)) < _
  rw [bridge, outer, mul_left_comm C σ, ← mul_add]
  exact mul_lt_mul_of_pos_left (hgap s hlo hhi) hσ

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
