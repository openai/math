import OAI.LinearAlgebra.SpectralBooks.PriceBlowup
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtensionTower

/-! # Spectral ultralimits over an arbitrary index set

To extend an infinite spectral space we index all finite sets of old sites,
so the index set of the pointed ultralimit need not be countable. A bounded
section represents a point; all distances and prices have the corresponding
ultrafilter limits. Exact midpoints pass to the limit coordinatewise.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SpectralUltralimit

open Filter Topology SiteTensor

variable {L : Type*} {K : Type*} [Field K]

/-- Uniformly bounded choices of a point in each pointed factor space. -/
structure Section (Z : L → Type*) [∀ i, MetricSpace (Z i)] (o : ∀ i, Z i) where
  val : ∀ i, Z i
  bound : ∃ R : ℝ, ∀ i, dist (o i) (val i) ≤ R

variable {Z : L → Type*} [∀ i, MetricSpace (Z i)] {o : ∀ i, Z i}

private theorem bound_dist (s t : Section Z o) :
    ∃ R : ℝ, ∀ i, dist (s.val i) (t.val i) ∈ Set.Icc 0 R := by
  obtain ⟨a, ha⟩ := s.bound
  obtain ⟨b, hb⟩ := t.bound
  exact ⟨a+b, fun i ↦ ⟨dist_nonneg, (dist_triangle _ (o i) _).trans
    (by rw [dist_comm (s.val i)]; exact add_le_add (ha i) (hb i))⟩⟩

private theorem dist_limit (U : Ultrafilter L) (s t : Section Z o) :
    Tendsto (fun i ↦ dist (s.val i) (t.val i)) (U : Filter L)
      (𝓝 (limUnder (U : Filter L) (fun i ↦ dist (s.val i) (t.val i)))) := by
  obtain ⟨R,hR⟩ := bound_dist s t
  obtain ⟨_, _, h⟩ := isCompact_Icc.ultrafilter_le_nhds' (U.map (fun i ↦ dist (s.val i) (t.val i)))
    (show Set.Icc (0 : ℝ) R ∈ U.map (fun i ↦ dist (s.val i) (t.val i)) from by
      change ∀ᶠ i in (U : Filter L), dist (s.val i) (t.val i) ∈ Set.Icc 0 R
      exact Eventually.of_forall hR)
  exact tendsto_nhds_limUnder ⟨_, h⟩

private structure Germ (U : Ultrafilter L) (Z : L → Type*) [∀ i, MetricSpace (Z i)]
    (o : ∀ i, Z i) extends Section Z o

private instance (U : Ultrafilter L) : PseudoMetricSpace (Germ U Z o) where
  dist s t := limUnder (U : Filter L) (fun i ↦ dist (s.val i) (t.val i))
  dist_self s := tendsto_nhds_unique (dist_limit U s.toSection s.toSection) (by simp)
  dist_comm s t := by simp only [dist_comm]
  dist_triangle s t z := le_of_tendsto_of_tendsto' (dist_limit U s.toSection z.toSection)
    ((dist_limit U s.toSection t.toSection).add (dist_limit U t.toSection z.toSection))
    (fun i ↦ dist_triangle _ _ _)

/-- The pointed metric ultralimit identifies bounded sections at zero
ultralimit distance. -/
def Space (U : Ultrafilter L) (Z : L → Type*) [∀ i, MetricSpace (Z i)] (o : ∀ i, Z i) : Type _ :=
  SeparationQuotient (Germ U Z o)

instance (U : Ultrafilter L) : MetricSpace (Space U Z o) :=
  inferInstanceAs (MetricSpace (SeparationQuotient (Germ U Z o)))

/-- Canonical map from a bounded section to its metric ultralimit point. -/
def point (U : Ultrafilter L) (s : Section Z o) : Space U Z o :=
  SeparationQuotient.mk (⟨s⟩ : Germ U Z o)

private theorem surj_point (U : Ultrafilter L) : Function.Surjective (point U (Z := Z) (o := o)) := by
  intro x
  obtain ⟨s, hs⟩ := SeparationQuotient.surjective_mk (X := Germ U Z o) x
  exact ⟨s.toSection, hs⟩

/-- Distances converge for every pair of representatives. -/
theorem tendsto_dist (U : Ultrafilter L) (s t : Section Z o) :
    Tendsto (fun i ↦ dist (s.val i) (t.val i)) (U : Filter L)
      (𝓝 (dist (point U s) (point U t))) :=
  dist_limit U s t

private def rep (U : Ultrafilter L) (x : Space U Z o) : Section Z o := (surj_point U x).choose

private theorem point_rep (U : Ultrafilter L) (x : Space U Z o) : point U (rep U x) = x :=
  (surj_point U x).choose_spec

private theorem rep_dist (U : Ultrafilter L) (x y : Space U Z o) :
    Tendsto (fun i ↦ dist ((rep U x).val i) ((rep U y).val i) / 1) (U : Filter L)
      (𝓝 (dist x y)) := by
  simpa only [div_one, point_rep] using tendsto_dist U (rep U x) (rep U y)

/-- The limiting spectral placement prices, over the original field. -/
def prices (U : Ultrafilter L) (H : ∀ i, SpectralPlacementPrices K (Z i)) (o : ∀ i, Z i) :
    SpectralPlacementPrices K (Space U Z o) :=
  SpectralPlacementPrices.blowupFamily H U (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
    (fun i x ↦ (rep U x).val i) (point U ⟨o, 0, fun _ ↦ (dist_self _).le⟩) (rep_dist U)

/-- Every finite placed price converges, independently of the chosen representatives. -/
theorem tendsto_price (U : Ultrafilter L) (H : ∀ i, SpectralPlacementPrices K (Z i))
    {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → Section Z o) :
    Tendsto (fun i ↦ (H i).price T (fun j ↦ (p j).val i)) (U : Filter L)
      (𝓝 ((prices U H o).price T (point U ∘ p))) := by
  let v := point U ∘ p
  have hv := SpectralPlacementPrices.tendsto_blowupFamily_price H U (fun _ ↦ 1)
    (fun _ ↦ zero_lt_one) (fun i x ↦ (rep U x).val i)
    (point U ⟨o, 0, fun _ ↦ (dist_self _).le⟩) (rep_dist U) T v
  simp only [div_one] at hv
  have d (j : I) : Tendsto (fun i ↦ dist ((p j).val i) ((rep U (v j)).val i)) (U : Filter L)
      (𝓝 0) := by
    simpa only [point_rep, v, Function.comp_apply, dist_self] using
      tendsto_dist U (p j) (rep U (v j))
  have hcost := tendsto_finsetSum Finset.univ (fun j _ ↦ (d j).mul_const
    (Real.logb 2 (Fintype.card (T.Leg j))))
  simp only [zero_mul, Finset.sum_const_zero] at hcost
  apply hv.congr_dist
  simp only [dist_comm ((H _).price T ((fun x ↦ (rep U x).val _) ∘ v))]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
    (Eventually.of_forall fun i ↦ (H i).transport T (fun j ↦ (p j).val i)
      (fun j ↦ (rep U (v j)).val i)) hcost

/-- A coordinatewise choice of exact midpoints gives an exact midpoint in the limit. -/
theorem exists_midpoints (U : Ultrafilter L) (o : ∀ i, Z i)
    (hm : ∀ i (a b : Z i), ∃ m, IsWireMidpoint a b m) :
    ∀ a b : Space U Z o, ∃ m, IsWireMidpoint a b m := by
  rintro a b
  obtain ⟨s, rfl⟩ := surj_point U a
  obtain ⟨t, rfl⟩ := surj_point U b
  choose mid hmid using fun i ↦ hm i (s.val i) (t.val i)
  obtain ⟨R,hR⟩ := s.bound
  obtain ⟨D,hD⟩ := bound_dist s t
  let m : Section Z o := ⟨mid, R + D / 2, fun i ↦ by
    have h := dist_triangle (o i) (s.val i) (mid i)
    rw [(hmid i).1] at h
    linarith [hR i, (hD i).2]⟩
  exact ⟨point U m, tendsto_nhds_unique (tendsto_dist U s m)
    (((tendsto_dist U s t).div_const 2).congr (fun i ↦ (hmid i).1.symm)),
    tendsto_nhds_unique (tendsto_dist U t m)
      (((tendsto_dist U s t).div_const 2).congr (fun i ↦ (hmid i).2.symm))⟩

end SpectralUltralimit

end

end SpectralBooks
end LinearAlgebra
end OAI
