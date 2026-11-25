import OAI.LinearAlgebra.SpectralBooks.MetricLimitPrice
import OAI.LinearAlgebra.SpectralBooks.PriceBlowup
import OAI.LinearAlgebra.SpectralBooks.SpectralDiagonal

/-!
# Pointed blow-ups with placement prices

A transport-controlled price on a finite list of sites descends to the pointed
metric ultralimit. Its value is the limit for every bounded representative
of a placement, so one can use the explicit page and geodesic representatives.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Book

open HyperbolicObstruction Filter
open scoped Topology Classical

variable {X : Type*} [MetricSpace X]

/-- Blow-up at `o` along positive scales `s n`, with distances divided by `s n`. -/
abbrev Blowup (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (o : X) :=
  MetricLimit.Space (U := ω) (X := fun n ↦ MetricScale.Space (s n)⁻¹ (inv_pos.mpr (hs n)) X)
    (o := fun _ ↦ ⟨o⟩)

/-- CAT(0) comparison holds in the pointed blow-up. -/
theorem blowup_catZero (hX : CATZero X) (ω : Ultrafilter ℕ) {s : ℕ → ℝ}
    (hs : ∀ n, 0 < s n) (o : X) : CATZero (Blowup ω hs o) :=
  MetricLimit.catZero (fun _ ↦ MetricScale.catZero hX)

/-- Bounded representatives in the rescaled spaces. -/
abbrev BlowupSection (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (o : X) :=
  MetricLimit.Bounded ω (fun n ↦ MetricScale.Space (s n)⁻¹ (inv_pos.mpr (hs n)) X) (fun _ ↦ ⟨o⟩)

variable (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (o : X)

private noncomputable def representative (b : Blowup ω hs o) : BlowupSection ω hs o :=
  (SeparationQuotient.surjective_mk b).choose

private theorem representative_point (b : Blowup ω hs o) :
    MetricLimit.point (representative ω hs o b) = b :=
  (SeparationQuotient.surjective_mk b).choose_spec

private theorem section_dist_tendsto (p q : BlowupSection ω hs o) :
    Tendsto (fun n ↦ dist (p.val n).val (q.val n).val / s n) (ω : Filter ℕ)
      (𝓝 (dist (MetricLimit.point p) (MetricLimit.point q))) := by
  simpa only [div_eq_inv_mul, ← MetricScale.dist_eq] using MetricLimit.tendsto_point_dist p q

private abbrev Stage (n : ℕ) (X : Type*) := MetricScale.Space (s n)⁻¹ (inv_pos.mpr (hs n)) X

private noncomputable def stagePrice {I : Type*} (price : (I → X) → ℝ) (n : ℕ) (u : I → Stage hs n X) : ℝ :=
  price (fun i ↦ (u i).val) / s n

private theorem stagePrice_transport {I : Type*} [Fintype I] (price : (I → X) → ℝ) (w : I → ℝ)
    (ht : ∀ u v, dist (price u) (price v) ≤ ∑ i, dist (u i) (v i) * w i)
    (n : ℕ) (u v : I → Stage hs n X) :
    dist (stagePrice hs price n u) (stagePrice hs price n v) ≤ ∑ i, dist (u i) (v i) * w i := by
  simp only [stagePrice, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (hs n)]
  rw [div_eq_inv_mul]
  simpa only [Real.dist_eq, MetricScale.dist_eq, mul_assoc, ← Finset.mul_sum] using
    mul_le_mul_of_nonneg_left (ht (fun i ↦ (u i).val) (fun i ↦ (v i).val)) (inv_nonneg.mpr (hs n).le)

/-- A finite placement price has a common value on the ultralimit for all
representatives of each site. The collapsed price and weighted transport
inequality are inherited from the original space. -/
theorem exists_blowup_placement_price {I : Type*} [Fintype I]
    (w : I → ℝ) (price : (I → X) → ℝ)
    (hz : ∀ p : X, price (fun _ ↦ p) = 0)
    (ht : ∀ u v, dist (price u) (price v) ≤ ∑ i, dist (u i) (v i) * w i) :
    ∃ D : (I → Blowup ω hs o) → ℝ,
      (∀ z : I → BlowupSection ω hs o,
        Tendsto (fun n ↦ price (fun i ↦ ((z i).val n).val) / s n) (ω : Filter ℕ)
          (𝓝 (D (fun i ↦ MetricLimit.point (z i))))) ∧
      (∀ b, D (fun _ ↦ b) = 0) ∧
      ∀ u v, dist (D u) (D v) ≤ ∑ i, dist (u i) (v i) * w i := by
  let H := stagePrice hs price
  have hzero (n : ℕ) (p : Stage hs n X) : H n (fun _ ↦ p) = 0 := by
    simp [H, stagePrice, hz]
  have hmove := stagePrice_transport hs price w ht
  exact ⟨_, tendsto_metricLimitPrice w H hzero hmove,
    metricLimitPrice_spec w H hzero hmove⟩

/-- A single diagonal price on all finite subsets of the blow-up. -/
noncomputable def blowupDiagonal (δ : Finset X → ℝ) (S : Finset (Blowup ω hs o)) : ℝ :=
  limUnder (ω : Filter ℕ) (fun n ↦ δ (S.image fun b ↦ ((representative ω hs o b).val n).val) / s n)

/-- Repeated limiting sites and different representatives give the same
diagonal price. Only the transport inequality at the given arity is needed. -/
theorem tendsto_blowupDiagonal {I : Type*} [Fintype I] [Nonempty I]
    (δ : Finset X → ℝ) (hz : ∀ x, δ {x} = 0)
    (ht : ∀ u v : I → X, dist (δ (Finset.univ.image u)) (δ (Finset.univ.image v))
      ≤ ∑ i, dist (u i) (v i)) (z : I → BlowupSection ω hs o) :
    Tendsto (fun n ↦ δ (Finset.univ.image fun i ↦ ((z i).val n).val) / s n)
      (ω : Filter ℕ)
      (𝓝 (blowupDiagonal ω hs o δ (Finset.univ.image fun i ↦ MetricLimit.point (z i)))) := by
  let b (i : I) := MetricLimit.point (z i)
  let r (i : I) := representative ω hs o (b i)
  obtain ⟨D, hD, _, _⟩ := exists_blowup_placement_price ω hs o (fun _ : I ↦ 1)
    (fun u ↦ δ (Finset.univ.image u))
    (by simpa only [Finset.image_const Finset.univ_nonempty] using hz) (by simpa using ht)
  have hc := hD r
  have he : (fun i ↦ MetricLimit.point (r i)) = b := funext (fun i ↦ representative_point _ _ _ _)
  rw [he] at hc
  have hval : blowupDiagonal ω hs o δ (Finset.univ.image b) = D b := by
    simpa only [blowupDiagonal, Finset.image_image, Function.comp_def, r] using hc.limUnder_eq
  rw [show (fun i ↦ MetricLimit.point (z i)) = b from rfl, hval]
  exact hD z

/-- The spectral prices on the complete list of sites of the pointed blow-up,
obtained from the field's original spectral prices at each rescaling. -/
noncomputable def blowupSpectralPrices {K : Type*} [Field K] (H : SpectralPlacementPrices K X) :
    SpectralPlacementPrices K (Blowup ω hs o) :=
  H.blowup ω s hs (fun n b ↦ ((representative ω hs o b).val n).val)
    (MetricLimit.point (⟨fun _ ↦ ⟨o⟩, 0, fun _ ↦ by simp⟩ : BlowupSection ω hs o))
    (fun p q ↦ by simpa only [representative_point] using
      section_dist_tendsto ω hs o (representative ω hs o p) (representative ω hs o q))

/-- Every choice of bounded representatives computes the constructed spectral
price of every placed tensor in the pointed blow-up. -/
theorem tendsto_blowupSpectralPrices {K : Type*} [Field K] (H : SpectralPlacementPrices K X)
    {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I K) (z : I → BlowupSection ω hs o) :
    Tendsto (fun n ↦ H.price T (fun i ↦ ((z i).val n).val) / s n) (ω : Filter ℕ)
      (𝓝 ((blowupSpectralPrices ω hs o H).price T (MetricLimit.point ∘ z))) := by
  refine tendsto_metricLimitPrice (fun i ↦ Real.logb 2 (Fintype.card (T.Leg i)))
    (stagePrice hs (H.price T)) ?_ ?_ z
  · intro n p
    simp [stagePrice, H.collapsed]
  · exact stagePrice_transport hs (H.price T) _ (H.transport T)

/-- Synchronized geodesic convexity of a tensor price persists for that
tensor in the pointed blow-up. -/
theorem blowupSpectralPrices_jointConvex {K : Type*} [Field K] (P : SpectralPlacementPrices K X)
    (hX : CATZero X) {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I K)
    (hc : ∀ u v : I → X, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      P.price T (fun i ↦ CATZero.segment hX (u i) (v i) t) ≤
        (1 - t) * P.price T u + t * P.price T v)
    (u v : I → Blowup ω hs o) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (blowupSpectralPrices ω hs o P).price T
        (fun i ↦ CATZero.segment (blowup_catZero hX ω hs o) (u i) (v i) t) ≤
      (1 - t) * (blowupSpectralPrices ω hs o P).price T u +
        t * (blowupSpectralPrices ω hs o P).price T v := by
  refine metricLimitPrice_jointConvex (fun _ ↦ MetricScale.catZero hX)
    (fun i ↦ Real.logb 2 (Fintype.card (T.Leg i))) (stagePrice hs (P.price T))
    (fun _ _ ↦ by simp [stagePrice, P.collapsed])
    (stagePrice_transport hs _ _ (P.transport T)) ?_ u v ht
  intro n x y r hr
  dsimp only [stagePrice]
  simp only [MetricScale.val_segment hX _ _ hr]
  simpa only [add_div, mul_div_assoc] using
    div_le_div_of_nonneg_right (hc (fun i ↦ (x i).val) (fun i ↦ (y i).val) r hr) (hs n).le

/-- Taking the price of the occupied diagonal commutes with the pointed blow-up.
The equality holds for every finite set of limit sites, regardless of its
ambient universe. -/
theorem blowupDiagonal_spectralPrices {K : Type*} [Field K] (P : SpectralPlacementPrices K X)
    (S : Finset (Blowup ω hs o)) (hS : S.Nonempty) :
    blowupDiagonal ω hs o P.diagonal S = (blowupSpectralPrices ω hs o P).diagonal S := by
  let b (i : Fin S.card) := (S.equivFin.symm i).val
  let z (i : Fin S.card) := representative ω hs o (b i)
  let _ : Nonempty (Fin S.card) := Fin.pos_iff_nonempty.mp hS.card_pos
  have hb : Finset.univ.image b = S := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).prop
    · intro hy
      exact ⟨S.equivFin ⟨y, hy⟩, by simp [b]⟩
  have hr : MetricLimit.point ∘ z = b := funext (fun i ↦ representative_point _ _ _ _)
  have h₁ := tendsto_blowupDiagonal ω hs o P.diagonal P.diagonal_singleton P.diagonal_transport z
  have hzset : (Finset.univ.image fun i ↦ MetricLimit.point (z i)) = S := by
    change Finset.univ.image (MetricLimit.point ∘ z) = S
    rw [hr, hb]
  rw [hzset] at h₁
  have h₂ := tendsto_blowupSpectralPrices ω hs o P (SiteTensor.Raw.diagonal (Fin S.card) K (Fin 2)) z
  rw [hr, SpectralPlacementPrices.price_binaryDiagonal_eq, hb] at h₂
  exact tendsto_nhds_unique h₁ (by simpa only [P.price_binaryDiagonal_eq] using h₂)

end Book

end SpectralBooks
end LinearAlgebra
end OAI
