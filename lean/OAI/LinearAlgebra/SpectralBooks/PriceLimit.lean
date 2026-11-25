import OAI.LinearAlgebra.SpectralBooks.TangentApproximation
import OAI.LinearAlgebra.SpectralBooks.Spectrum

/-!
# Joint limits of placement prices in a pointed rescaling

The transport bound for the price of a placed tensor controls its rescaled
value by the sum of the rescaled distances of the indices to a single site.
Thus one ultrafilter can be used for every placement and every tensor. The
transport bound and the zero price of a collapsed placement pass to the limit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Topology HyperbolicObstruction

/-- The limit along a common ultrafilter of the price of a placed tensor. -/
noncomputable def blowupPrice {I X Y A : Type*} (u : Ultrafilter I) (scale : I → ℝ)
    (point : I → Y → X) (price : (A → X) → ℝ) (x : A → Y) : ℝ :=
  limUnder (u : Filter I) (fun i => price (point i ∘ x) / scale i)

/-- The limit along a common ultrafilter of the price of a placed tensor. -/
noncomputable def blowupPriceFamily {I Y A : Type*} {X : I → Type*} (u : Ultrafilter I) (scale : I → ℝ)
    (point : ∀ i, Y → X i) (price : ∀ i, (A → X i) → ℝ) (x : A → Y) : ℝ :=
  limUnder (u : Filter I) (fun i => price i (point i ∘ x) / scale i)

/-- A price obeying the finite weighted transport bound has a limit at every
placement in a pointed blowup. In the spectral-space application the weight of
an index is the base-two logarithm of its local dimension. -/
theorem blowupPriceFamily_spec {I Y A : Type*} {X : I → Type*} [∀ i, PseudoMetricSpace (X i)] [PseudoMetricSpace Y]
    [Fintype A] (u : Ultrafilter I) (scale : I → ℝ) (hs : ∀ i, 0 < scale i)
    (point : ∀ i, Y → X i) (y₀ : Y)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter I) (𝓝 (dist p q)))
    (w : A → ℝ) (price : ∀ i, (A → X i) → ℝ)
    (hzero : ∀ i (p : X i), price i (fun _ => p) = 0)
    (htransport : ∀ i x y, dist (price i x) (price i y) ≤ ∑ a, dist (x a) (y a) * w a) :
    (∀ x : A → Y, Tendsto (fun i => price i (point i ∘ x) / scale i)
      (u : Filter I) (𝓝 (blowupPriceFamily u scale point price x))) ∧
    (∀ y : Y, blowupPriceFamily u scale point price (fun _ => y) = 0) ∧
    ∀ x y : A → Y, dist (blowupPriceFamily u scale point price x) (blowupPriceFamily u scale point price y)
      ≤ ∑ a, dist (x a) (y a) * w a := by
  let v (x : A → Y) (i : I) := price i (point i ∘ x) / scale i
  let cost (x y : A → Y) (i : I) := ∑ a, (dist (point i (x a)) (point i (y a)) / scale i) * w a
  have hcost (x y : A → Y) : Tendsto (cost x y) (u : Filter I) (𝓝 (∑ a, dist (x a) (y a) * w a)) :=
    tendsto_finsetSum _ (fun a _ => (hdist (x a) (y a)).mul_const (w a))
  have hle (x y : A → Y) (i : I) : dist (v x i) (v y i) ≤ cost x y i := by
    have hh := div_le_div_of_nonneg_right (htransport i (point i ∘ x) (point i ∘ y)) (hs i).le
    simp only [v, cost, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (hs i)]
    simpa only [Real.dist_eq, Finset.sum_div, div_mul_eq_mul_div, Function.comp_apply] using hh
  have hconstant (y : Y) (i : I) : v (fun _ => y) i = 0 := by
    change price i (fun _ => point i y) / scale i = 0
    rw [hzero, zero_div]
  have hlim (x : A → Y) : Tendsto (v x) (u : Filter I) (𝓝 (blowupPriceFamily u scale point price x)) := by
    let c : A → Y := fun _ => y₀
    let B := (∑ a, dist (x a) (c a) * w a) + 1
    have hB : ∀ᶠ i in (u : Filter I), cost x c i < B :=
      (hcost x c).eventually (gt_mem_nhds (lt_add_one _))
    have hmem : Metric.closedBall (0 : ℝ) B ∈ u.map (v x) := by
      apply hB.mono
      intro i hi
      have h := hle x c i
      rw [show v c i = 0 from hconstant y₀ i] at h
      exact h.trans hi.le
    obtain ⟨a, _, ha⟩ := (isCompact_closedBall (0 : ℝ) B).ultrafilter_le_nhds' _ hmem
    exact tendsto_nhds_limUnder ⟨a, ha⟩
  refine ⟨hlim, fun y => tendsto_nhds_unique (hlim _)
    (tendsto_const_nhds.congr fun i => (hconstant y i).symm), ?_⟩
  exact fun x y => le_of_tendsto_of_tendsto ((hlim x).dist (hlim y)) (hcost x y)
    (Eventually.of_forall (hle x y))

/-- A price obeying the finite weighted transport bound has a limit at every
placement in a pointed blowup. In the spectral-space application the weight of
an index is the base-two logarithm of its local dimension. -/
theorem blowupPrice_spec {I X Y A : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [Fintype A] (u : Ultrafilter I) (scale : I → ℝ) (hs : ∀ i, 0 < scale i)
    (point : I → Y → X) (y₀ : Y)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter I) (𝓝 (dist p q)))
    (w : A → ℝ) (price : (A → X) → ℝ)
    (hzero : ∀ p : X, price (fun _ => p) = 0)
    (htransport : ∀ x y, dist (price x) (price y) ≤ ∑ a, dist (x a) (y a) * w a) :
    (∀ x : A → Y, Tendsto (fun i => price (point i ∘ x) / scale i)
      (u : Filter I) (𝓝 (blowupPrice u scale point price x))) ∧
    (∀ y : Y, blowupPrice u scale point price (fun _ => y) = 0) ∧
    ∀ x y : A → Y, dist (blowupPrice u scale point price x) (blowupPrice u scale point price y)
      ≤ ∑ a, dist (x a) (y a) * w a :=
  blowupPriceFamily_spec u scale hs point y₀ hdist w (fun _ => price)
    (fun _ => hzero) (fun _ => htransport)

/-- Compatibility of prices with grouping sites or inserting trivial slots
passes through a blowup along the same map of site labels. -/
theorem blowupPriceFamily_reindex {I Y A B : Type*} {X : I → Type*} (u : Ultrafilter I) (scale : I → ℝ)
    (point : ∀ i, Y → X i) (e : A → B) (P : ∀ i, (A → X i) → ℝ) (Q : ∀ i, (B → X i) → ℝ)
    (he : ∀ i (x : B → X i), P i (x ∘ e) = Q i x) (y : B → Y) :
    blowupPriceFamily u scale point P (y ∘ e) = blowupPriceFamily u scale point Q y := by
  unfold blowupPriceFamily
  congr 1
  funext i
  rw [← he i (point i ∘ y)]
  rfl

/-- A wire, whose price is the distance of its two endpoints, retains exactly
the distance of the limiting placement. -/
theorem blowupPriceFamily_wire {I Y : Type*} {X : I → Type*} [∀ i, PseudoMetricSpace (X i)] [PseudoMetricSpace Y]
    (u : Ultrafilter I) (scale : I → ℝ) (point : ∀ i, Y → X i)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter I) (𝓝 (dist p q))) (x : Fin 2 → Y) :
    blowupPriceFamily u scale point (fun i (z : Fin 2 → X i) => dist (z 0) (z 1)) x = dist (x 0) (x 1) :=
  (hdist (x 0) (x 1)).limUnder_eq

/-- On a fixed set of sites, joint convergence of tensor prices and their
common normalization gives a single spectral point for all the limiting
prices. Only tensors admitting a restriction to the unit need a log-price.
The limiting normalization may vanish. -/
theorem normalizedSpectralPrice_limit {I S R : Type*} [Semiring S]
    (restricts : S → S → Prop) (hrank : ∀ x, ∃ n : ℕ, restricts x n)
    (u : Ultrafilter I) (φ : I → normalizedSpectrum restricts) {c : I → ℝ} {d : ℝ}
    (hc : Tendsto c (u : Filter I) (𝓝 d)) (tensor : R → S) (hunit : ∀ t, restricts 1 (tensor t))
    (price : R → ℝ)
    (hprice : ∀ x, Tendsto (fun i => c i * Real.logb 2 ((φ i).val (tensor x) : ℝ))
      (u : Filter I) (𝓝 (price x))) :
    ∃ ψ : normalizedSpectrum restricts, ∀ x, price x = d * Real.logb 2 (ψ.val (tensor x) : ℝ) := by
  let : CompactSpace (normalizedSpectrum restricts) :=
    isCompact_iff_compactSpace.mp (isCompact_normalizedSpectrum restricts hrank)
  obtain ⟨ψ, _, hψ⟩ := isCompact_univ.ultrafilter_le_nhds' (u.map φ) (show Set.univ ∈ u.map φ from Filter.univ_mem)
  have hφ : Tendsto φ (u : Filter I) (𝓝 ψ) := hψ
  exact ⟨ψ, fun x => tendsto_nhds_unique (hprice x)
    (hc.mul (((continuous_log_price (hunit x)).tendsto ψ).comp hφ))⟩

/-- Finite sets of distinct limiting sites have distinct representatives
eventually, even when the maps approximating the entire cone are not injective. -/
theorem eventually_injOn_of_rescaled_dist {I Y : Type*} {X : I → Type*} [∀ i, PseudoMetricSpace (X i)] [MetricSpace Y]
    (l : Filter I) (scale : I → ℝ) (point : ∀ i, Y → X i)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      l (𝓝 (dist p q))) (s : Finset Y) :
    ∀ᶠ i in l, Set.InjOn (point i) s := by
  have hev (p q : Y) : ∀ᶠ i in l, point i p = point i q → p = q := by
    by_cases hpq : p = q
    · exact Eventually.of_forall fun _ _ => hpq
    · filter_upwards [(hdist p q).eventually (lt_mem_nhds (dist_pos.mpr hpq))] with i hi he
      simp [he] at hi
  filter_upwards [(s.eventually_all).2 fun p _ => (s.eventually_all).2 fun q _ => hev p q]
    with i hi
  exact fun p hp q hq => hi p hp q hq

/-- If the original prices on each placement of distinct sites admit a common
spectral point normalized by the binary full diagonal, the same is true after
rescaling and passing to the tangent limit. All tensors on the finite set of
sites use the same limiting spectral point. -/
theorem blowupPriceFamily_spectral {I Y A S R : Type*} {X : I → Type*}
    [∀ i, PseudoMetricSpace (X i)] [MetricSpace Y] [Fintype A] [Semiring S]
    (restricts : S → S → Prop) (hrank : ∀ x, ∃ n : ℕ, restricts x n)
    (u : Ultrafilter I) (scale : I → ℝ) (point : ∀ i, Y → X i)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter I) (𝓝 (dist p q)))
    (tensor : R → S) (hunit : ∀ t, restricts 1 (tensor t))
    (δ : ∀ i, (A → X i) → ℝ) (price : R → ∀ i, (A → X i) → ℝ)
    (hnormal : ∀ i (x : A → X i), Function.Injective x → ∃ φ : normalizedSpectrum restricts,
      ∀ t, price t i x = δ i x * Real.logb 2 (φ.val (tensor t) : ℝ))
    (p : A → Y) (hp : Function.Injective p)
    (hδ : Tendsto (fun i => δ i (point i ∘ p) / scale i) (u : Filter I)
      (𝓝 (blowupPriceFamily u scale point δ p)))
    (hprice : ∀ t, Tendsto (fun i => price t i (point i ∘ p) / scale i)
      (u : Filter I) (𝓝 (blowupPriceFamily u scale point (price t) p))) :
    ∃ ψ : normalizedSpectrum restricts, ∀ t,
      blowupPriceFamily u scale point (price t) p = blowupPriceFamily u scale point δ p * Real.logb 2 (ψ.val (tensor t) : ℝ) := by
  classical
  let valid (i : I) (φ : normalizedSpectrum restricts) :=
    ∀ t, price t i (point i ∘ p) = δ i (point i ∘ p) * Real.logb 2 (φ.val (tensor t) : ℝ)
  have hvalid : ∀ᶠ i in (u : Filter I), ∃ φ, valid i φ := by
    filter_upwards [eventually_injOn_of_rescaled_dist (u : Filter I) scale point hdist
      (Finset.univ.image p)] with i hi
    apply hnormal
    intro a b he
    exact hp (hi (Finset.mem_image_of_mem p (Finset.mem_univ a))
      (Finset.mem_image_of_mem p (Finset.mem_univ b)) he)
  obtain ⟨_, φ₀, _⟩ := hvalid.exists
  let φ (i : I) := if h : ∃ φ, valid i φ then h.choose else φ₀
  have he : ∀ᶠ i in (u : Filter I), valid i (φ i) := hvalid.mono fun i hi => by
    simpa only [φ, dite_eq_left hi] using hi.choose_spec
  apply normalizedSpectralPrice_limit restricts hrank u φ hδ tensor hunit
  intro t
  apply (hprice t).congr'
  filter_upwards [he] with i hi
  rw [hi t]
  ring

/-- The scales and maps can be chosen once for all tensor prices on all finite
placements. The ultrafilter may be any refinement of the directed filter of
finite sets and precision indices. -/
theorem tangentCone_joint_price_limits {X : Type*} [MetricSpace X] (h : CATZero X) (o : X)
    (u : Ultrafilter (Finset (TangentCone h o) × ℕ)) (hu : (u : Filter (Finset (TangentCone h o) × ℕ)) ≤ atTop) :
    ∃ (scale : Finset (TangentCone h o) × ℕ → ℝ)
      (point : Finset (TangentCone h o) × ℕ → TangentCone h o → X),
      (∀ i, 0 < scale i) ∧ Tendsto scale (u : Filter (Finset (TangentCone h o) × ℕ)) (𝓝[>] 0) ∧
      (∀ i, point i (TangentCone.vertex h o) = o) ∧
      (∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
        (u : Filter (Finset (TangentCone h o) × ℕ)) (𝓝 (dist p q))) ∧
      ∀ (n : ℕ) (w : Fin n → ℝ) (price : (Fin n → X) → ℝ),
        (∀ p : X, price (fun _ => p) = 0) →
        (∀ x y, dist (price x) (price y) ≤ ∑ a, dist (x a) (y a) * w a) →
        ∀ x : Fin n → TangentCone h o, Tendsto (fun i => price (point i ∘ x) / scale i)
          (u : Filter (Finset (TangentCone h o) × ℕ)) (𝓝 (blowupPrice u scale point price x)) := by
  obtain ⟨scale, point, hs, hshrink, hv, hd⟩ := tangentCone_pointed_approx h o
  have hdist (p q) := (hd p q).mono_left hu
  refine ⟨scale, point, hs, hshrink.mono_left hu, hv, hdist, ?_⟩
  intro n w price hz ht
  exact (blowupPrice_spec u scale hs point (TangentCone.vertex h o) hdist w price hz ht).1

end SpectralBooks
end LinearAlgebra
end OAI
