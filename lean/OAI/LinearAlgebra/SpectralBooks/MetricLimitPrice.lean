import OAI.Geometry.HyperbolicGroups.MetricProduct

/-!
# Placement prices on a pointed metric ultralimit

For a fixed tensor, the vanishing of its price at a collapsed placement and
the finite-index transport inequality both pass to the metric ultralimit.
Every choice of bounded representatives yields the same price. The proof
uses a single ultrafilter for all finite index types and all price functions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open Filter Topology HyperbolicObstruction MetricLimit

universe u v
variable {U : Ultrafilter ℕ} {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {o : ∀ n, X n}
variable {A : Type v} [Fintype A]

private def sectionCost (w : A → ℝ) (p q : A → Bounded U X o) (n : ℕ) : ℝ :=
  ∑ a, dist ((p a).val n) ((q a).val n) * w a

private theorem tendsto_sectionCost (w : A → ℝ) (p q : A → Bounded U X o) :
    Tendsto (sectionCost w p q) (U : Filter ℕ)
      (𝓝 (∑ a, dist (point (p a)) (point (q a)) * w a)) :=
  tendsto_finsetSum _ (fun a _ ↦ (tendsto_point_dist (p a) (q a)).mul_const (w a))

private def sectionPrice (H : (n : ℕ) → (A → X n) → ℝ) (p : A → Bounded U X o) : ℝ :=
  limUnder (U : Filter ℕ) (fun n ↦ H n (fun a ↦ (p a).val n))

private theorem tendsto_sectionPrice (w : A → ℝ) (H : (n : ℕ) → (A → X n) → ℝ)
    (hzero : ∀ n (x : X n), H n (fun _ ↦ x) = 0)
    (hmove : ∀ n p q, dist (H n p) (H n q) ≤ ∑ a, dist (p a) (q a) * w a)
    (p : A → Bounded U X o) :
    Tendsto (fun n ↦ H n (fun a ↦ (p a).val n)) (U : Filter ℕ) (𝓝 (sectionPrice H p)) := by
  let base : Bounded U X o := ⟨o, 0, by simp⟩
  let B := (∑ a, dist (point (p a)) (point base) * w a) + 1
  have hb : ∀ᶠ n in (U : Filter ℕ), sectionCost w p (fun _ ↦ base) n < B :=
    (tendsto_sectionCost w p (fun _ ↦ base)).eventually_lt_const (lt_add_one _)
  let f (n : ℕ) := H n (fun a ↦ (p a).val n)
  have hm : Metric.closedBall (0 : ℝ) B ∈ U.map f := by
    apply hb.mono
    intro n hn
    have h := hmove n (fun a ↦ (p a).val n) (fun _ ↦ o n)
    rw [hzero] at h
    exact h.trans hn.le
  obtain ⟨_, _, ht⟩ := (isCompact_closedBall (0 : ℝ) B).ultrafilter_le_nhds' _ hm
  exact tendsto_nhds_limUnder ⟨_, ht⟩

private theorem dist_sectionPrice_le (w : A → ℝ) (H : (n : ℕ) → (A → X n) → ℝ)
    (hzero : ∀ n (x : X n), H n (fun _ ↦ x) = 0)
    (hmove : ∀ n p q, dist (H n p) (H n q) ≤ ∑ a, dist (p a) (q a) * w a)
    (p q : A → Bounded U X o) :
    dist (sectionPrice H p) (sectionPrice H q) ≤ ∑ a, dist (point (p a)) (point (q a)) * w a :=
  le_of_tendsto_of_tendsto' ((tendsto_sectionPrice w H hzero hmove p).dist
    (tendsto_sectionPrice w H hzero hmove q)) (tendsto_sectionCost w p q)
    (fun n ↦ hmove n _ _)

private def representative (x : Space (U := U) (X := X) (o := o)) : Bounded U X o :=
  (SeparationQuotient.surjective_mk x).choose

private theorem point_representative (x : Space (U := U) (X := X) (o := o)) :
    point (representative x) = x := (SeparationQuotient.surjective_mk x).choose_spec

/-- The ultralimit price at a placement of points of the separated metric ultralimit. -/
def metricLimitPrice (H : (n : ℕ) → (A → X n) → ℝ)
    (q : A → Space (U := U) (X := X) (o := o)) : ℝ :=
  sectionPrice H (representative ∘ q)

/-- For any bounded representatives of the placed indices, the prices
converge to their value on the separated metric ultralimit. -/
theorem tendsto_metricLimitPrice (w : A → ℝ) (H : (n : ℕ) → (A → X n) → ℝ)
    (hzero : ∀ n (x : X n), H n (fun _ ↦ x) = 0)
    (hmove : ∀ n p q, dist (H n p) (H n q) ≤ ∑ a, dist (p a) (q a) * w a)
    (p : A → Bounded U X o) :
    Tendsto (fun n ↦ H n (fun a ↦ (p a).val n)) (U : Filter ℕ)
      (𝓝 (metricLimitPrice H (point ∘ p))) := by
  have h := dist_sectionPrice_le w H hzero hmove p (representative ∘ point ∘ p)
  simp only [Function.comp_apply, point_representative, dist_self, zero_mul, Finset.sum_const_zero,
    dist_le_zero] at h
  rw [metricLimitPrice, ← h]
  exact tendsto_sectionPrice w H hzero hmove p

/-- The weighted transport inequality and the zero price for a collapsed
placement hold on all points of the metric ultralimit. -/
theorem metricLimitPrice_spec (w : A → ℝ) (H : (n : ℕ) → (A → X n) → ℝ)
    (hzero : ∀ n (x : X n), H n (fun _ ↦ x) = 0)
    (hmove : ∀ n p q, dist (H n p) (H n q) ≤ ∑ a, dist (p a) (q a) * w a) :
    (∀ x : Space (U := U) (X := X) (o := o), metricLimitPrice H (fun _ ↦ x) = 0) ∧
    ∀ p q : A → Space (U := U) (X := X) (o := o),
      dist (metricLimitPrice H p) (metricLimitPrice H q) ≤ ∑ a, dist (p a) (q a) * w a := by
  refine ⟨fun x ↦ ?_, fun p q ↦ ?_⟩
  · apply tendsto_nhds_unique (tendsto_sectionPrice w H hzero hmove (fun _ ↦ representative x))
    exact tendsto_const_nhds.congr (fun n ↦ (hzero n _).symm)
  · simpa only [metricLimitPrice, Function.comp_apply, point_representative] using
      dist_sectionPrice_le w H hzero hmove (representative ∘ p) (representative ∘ q)

/-- Convexity along synchronized geodesics passes to the quotient prices in a
CAT(0) ultralimit. -/
theorem metricLimitPrice_jointConvex (hX : ∀ n, CATZero (X n)) (w : A → ℝ)
    (H : (n : ℕ) → (A → X n) → ℝ) (hzero : ∀ n (x : X n), H n (fun _ ↦ x) = 0)
    (hmove : ∀ n p q, dist (H n p) (H n q) ≤ ∑ a, dist (p a) (q a) * w a)
    (hconv : ∀ n p q t, t ∈ Set.Icc (0 : ℝ) 1 →
      H n (fun a ↦ CATZero.segment (hX n) (p a) (q a) t) ≤ (1-t) * H n p + t * H n q)
    (p q : A → Space (U := U) (X := X) (o := o)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    metricLimitPrice H (fun a ↦ CATZero.segment (MetricLimit.catZero hX) (p a) (q a) t) ≤
      (1-t) * metricLimitPrice H p + t * metricLimitPrice H q := by
  let m (a : A) := MetricLimit.segment hX (representative (p a)) (representative (q a)) t
  have hm := tendsto_metricLimitPrice w H hzero hmove m
  have he (a : A) : point (m a) = CATZero.segment (MetricLimit.catZero hX) (p a) (q a) t := by
    simp only [m, point_segment hX _ _ ht, point_representative]
  rw [show point ∘ m = _ by exact funext he] at hm
  apply le_of_tendsto_of_tendsto' hm
    (((tendsto_sectionPrice w H hzero hmove (representative ∘ p)).const_mul (1-t)).add
      ((tendsto_sectionPrice w H hzero hmove (representative ∘ q)).const_mul t))
  intro n
  simpa only [Function.comp_apply, m, segment_val hX _ _ ht] using
    hconv n (fun a ↦ (representative (p a)).val n) (fun a ↦ (representative (q a)).val n) t ht

/-- A unit binary wire has price equal to the distance in the actual metric ultralimit. -/
theorem metricLimitPrice_wire (p : Fin 2 → Space (U := U) (X := X) (o := o)) :
    metricLimitPrice (fun _ q ↦ dist (q 0) (q 1)) p = dist (p 0) (p 1) := by
  have h := tendsto_point_dist (representative (p 0)) (representative (p 1))
  rw [point_representative, point_representative] at h
  exact h.limUnder_eq

end

end

end SpectralBooks
end LinearAlgebra
end OAI
