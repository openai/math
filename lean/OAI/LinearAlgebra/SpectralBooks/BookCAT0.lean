import OAI.Geometry.IntegralFillings.Geometry.Comparison
import OAI.LinearAlgebra.SpectralBooks.FacetCube
import Mathlib.Analysis.Convex.Strong

/-!
# Geodesic uniqueness and squared-distance convexity on the doubled cubes

We use the repository's metric triangle-comparison formulation of CAT(0).
Its squared-distance inequality yields the midpoint identification and the
agreement on the inner cube used in the proof of the book theorem.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set SharpIntegralFillings

variable {X : Type*} [MetricSpace X]

/-- A point at prescribed complementary fractions of the endpoint distance
coincides with the comparison geodesic at the same parameter. -/
theorem cat0_eq_fraction_point
    {γ : X → X → ℝ → X}
    (hγ : ∀ a b q t, t ∈ Icc (0 : ℝ) 1 → dist (γ a b t) q ^ 2 ≤
      (1 - t) * dist a q ^ 2 + t * dist b q ^ 2 - t * (1 - t) * dist a b ^ 2)
    {a b q : X} {t : ℝ} (ht : t ∈ Icc 0 1)
    (ha : dist a q = t * dist a b) (hb : dist b q = (1 - t) * dist a b) :
    γ a b t = q := by
  have h := hγ a b q t ht
  rw [ha, hb] at h
  ring_nf at h
  exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := γ a b t) (y := q)])

/-- The auxiliary site between the center and an outer corner is their unique
midpoint as soon as both wire distances are bounded by half the total. -/
theorem cat0_auxiliary_midpoint (hX : IsCAT0 X) {a b q : X} {r : ℝ}
    (hab : dist a b = 2 * r) (ha : dist a q ≤ r) (hb : dist b q ≤ r) :
    dist a q = r ∧ dist b q = r ∧
      ∀ p, dist a p ≤ r → dist b p ≤ r → p = q := by
  obtain ⟨γ, _, hγ⟩ := hX.exists_squared_distance_convex
  have mid {p : X} (h₁ : dist a p ≤ r) (h₂ : dist b p ≤ r) :
      dist a p = r ∧ dist b p = r := by
    have h := dist_triangle a p b
    rw [dist_comm p b, hab] at h
    constructor <;> linarith
  obtain ⟨ha', hb'⟩ := mid ha hb
  refine ⟨ha', hb', fun p hp₁ hp₂ ↦ ?_⟩
  obtain ⟨hp₁', hp₂'⟩ := mid hp₁ hp₂
  have hq := cat0_eq_fraction_point hγ (a := a) (b := b) (q := q) (t := 1 / 2) (by norm_num)
    (by rw [ha', hab]; ring) (by rw [hb', hab]; ring)
  have hp := cat0_eq_fraction_point hγ (a := a) (b := b) (q := p) (t := 1 / 2) (by norm_num)
    (by rw [hp₁', hab]; ring) (by rw [hp₂', hab]; ring)
  exact hp.symm.trans hq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : Set E} {f g : E → X}

/-- The image of a Euclidean line segment in a convex isometric patch follows
the comparison geodesic in the ambient CAT(0) space. -/
private theorem map_lineMap_eq_fraction
    {γ : X → X → ℝ → X}
    (hγ : ∀ a b q t, t ∈ Icc (0 : ℝ) 1 → dist (γ a b t) q ^ 2 ≤
      (1 - t) * dist a q ^ 2 + t * dist b q ^ 2 - t * (1 - t) * dist a b ^ 2)
    (hc : Convex ℝ C) (hf : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) = dist x y)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) {t : ℝ} (ht : t ∈ Icc 0 1) :
    γ (f x) (f y) t = f (AffineMap.lineMap x y t) := by
  have hz := hc.lineMap_mem hx hy ht
  apply cat0_eq_fraction_point hγ ht
  · rw [hf x hx _ hz, hf x hx _ hy, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht.1]
  · rw [hf y hy _ hz, hf x hx _ hy, dist_right_lineMap, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2)]

/-- Isometric embeddings of a convex Euclidean patch into the same CAT(0)
space agree on the convex hull of any sites at which they agree. -/
theorem cat0_patch_eqOn_convexHull (hX : IsCAT0 X) (hc : Convex ℝ C)
    (hf : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) = dist x y)
    (hg : ∀ x ∈ C, ∀ y ∈ C, dist (g x) (g y) = dist x y)
    {V : Set E} (hVC : V ⊆ C) (hfg : V.EqOn f g) : (convexHull ℝ V).EqOn f g := by
  obtain ⟨γ, _, hγ⟩ := hX.exists_squared_distance_convex
  have hconv : Convex ℝ {x : E | x ∈ C ∧ f x = g x} := by
    intro x hx y hy a b ha hb hab
    have ht : b ∈ Icc (0 : ℝ) 1 := ⟨hb, by linarith⟩
    have heq := map_lineMap_eq_fraction hγ hc hf hx.1 hy.1 ht
    rw [hx.2, hy.2, map_lineMap_eq_fraction hγ hc hg hx.1 hy.1 ht] at heq
    refine ⟨hc hx.1 hy.1 ha hb hab, ?_⟩
    simpa only [AffineMap.lineMap_apply_module, show 1 - b = a by linarith] using heq.symm
  have hV : V ⊆ {x : E | x ∈ C ∧ f x = g x} := fun v hv ↦ ⟨hVC hv, hfg hv⟩
  exact fun _ hx ↦ (convexHull_min hV hconv hx).2

/-- On a convex isometric patch, the squared distance to any ambient point
is strongly convex with parameter two. -/
theorem cat0_patch_strongConvexOn_dist_sq (hX : IsCAT0 X) (hc : Convex ℝ C)
    (hf : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) = dist x y) (q : X) :
    StrongConvexOn C 2 (fun x ↦ dist (f x) q ^ 2) := by
  obtain ⟨γ, _, hγ⟩ := hX.exists_squared_distance_convex
  refine ⟨hc, ?_⟩
  intro x hx y hy a b ha hb hab
  have ht : b ∈ Icc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  have h := hγ (f x) (f y) q b ht
  rw [map_lineMap_eq_fraction hγ hc hf hx hy ht, AffineMap.lineMap_apply_module,
    show 1 - b = a by linarith, hf x hx y hy, dist_eq_norm] at h
  simpa [mul_comm b a] using h

omit [NormedSpace ℝ E] in
/-- Distance to a fixed point is 1-Lipschitz on an isometric patch. -/
theorem patch_lipschitzOn_dist
    (hf : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) = dist x y) (q : X) :
    LipschitzOnWith 1 (fun x ↦ dist (f x) q) C := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  simpa [hf _ hx _ hy] using dist_dist_dist_le_left (f x) (f y) q

/-- Distance to a fixed point is convex on a Euclidean patch in a CAT(0) space. -/
theorem cat0_patch_convexOn_dist (hX : IsCAT0 X) (hc : Convex ℝ C)
    (hf : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) = dist x y) (q : X) :
    ConvexOn ℝ C (fun x ↦ dist (f x) q) := by
  refine ⟨hc, ?_⟩
  intro x hx y hy a b ha hb hab
  have hstrong := (cat0_patch_strongConvexOn_dist_sq hX hc hf q).2 hx hy ha hb hab
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self, one_mul,
    smul_eq_mul] at hstrong
  have hd := abs_dist_sub_le (f x) (f y) q
  rw [hf _ hx _ hy, dist_eq_norm] at hd
  have hsquare := (sq_le_sq' (abs_le.mp hd).1 (abs_le.mp hd).2)
  have hprod := mul_le_mul_of_nonneg_left hsquare (mul_nonneg ha hb)
  simp only [smul_eq_mul]
  refine (sq_le_sq₀ dist_nonneg
    (add_nonneg (mul_nonneg ha dist_nonneg) (mul_nonneg hb dist_nonneg))).mp ?_
  apply hstrong.trans
  calc
    _ ≤ a * dist (f x) q ^ 2 + b * dist (f y) q ^ 2 -
        a * b * (dist (f x) q - dist (f y) q) ^ 2 := by linarith
    _ = _ := by rw [show a = 1 - b by linarith]; ring

section Cubes

variable {ι : Type*} [Fintype ι]

/-- The finite family of corners of the cube of half-side length `a`. -/
noncomputable def coordinateCubeCorners (ι : Type*) [Fintype ι] (a : ℝ) :
    Finset (EuclideanSpace ℝ ι) := by
  classical
  exact (Fintype.piFinset fun _ : ι ↦ ({-a, a} : Finset ℝ)).map
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toEmbedding

/-- Each coordinate interval is the segment between its endpoints, so the
coordinate cube is the convex hull of the finite family of sign choices. -/
theorem convexHull_coordinateCubeCorners {a : ℝ} (ha : 0 ≤ a) :
    convexHull ℝ (coordinateCubeCorners ι a : Set (EuclideanSpace ℝ ι)) =
      coordinateCube ι a := by
  classical
  let e := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  rw [coordinateCubeCorners, Finset.coe_map, Fintype.coe_piFinset]
  change convexHull ℝ (e.toLinearMap '' _) = _
  rw [← e.toLinearMap.image_convexHull, convexHull_pi]
  simp only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair, segment_eq_Icc (by linarith : -a ≤ a)]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    exact hy j (mem_univ j)
  · intro hx
    exact ⟨WithLp.ofLp x, fun j _ ↦ hx j, rfl⟩

theorem convex_coordinateCube {a : ℝ} (ha : 0 ≤ a) : Convex ℝ (coordinateCube ι a) := by
  rw [← convexHull_coordinateCubeCorners ha]
  exact convex_convexHull _ _

/-- Agreement at the inner corners forces agreement at every point of the
inner cube for two isometries on the doubled cube in the same CAT(0) space. -/
theorem cat0_doubled_charts_agree (hX : IsCAT0 X) {f g : EuclideanSpace ℝ ι → X}
    (hf : ∀ x ∈ coordinateCube ι 2, ∀ y ∈ coordinateCube ι 2, dist (f x) (f y) = dist x y)
    (hg : ∀ x ∈ coordinateCube ι 2, ∀ y ∈ coordinateCube ι 2, dist (g x) (g y) = dist x y)
    (hfg : (coordinateCubeCorners ι 1 : Set (EuclideanSpace ℝ ι)).EqOn f g) :
    (coordinateCube ι 1).EqOn f g := by
  have hcorners : (coordinateCubeCorners ι 1 : Set (EuclideanSpace ℝ ι)) ⊆ coordinateCube ι 1 := by
    rw [← convexHull_coordinateCubeCorners (by norm_num : (0 : ℝ) ≤ 1)]
    exact subset_convexHull _ _
  have hinner : coordinateCube ι 1 ⊆ coordinateCube ι 2 :=
    coordinateCube_one_subset_interior_two.trans interior_subset
  rw [← convexHull_coordinateCubeCorners (by norm_num : (0 : ℝ) ≤ 1)]
  exact cat0_patch_eqOn_convexHull hX (convex_coordinateCube (by norm_num)) hf hg
    (hcorners.trans hinner) hfg

/-- In the doubled-grid construction each auxiliary corner has wire distances
at most `‖z‖` to the center and to both outer copies of `2z`. These wire bounds
alone identify the two embeddings on the entire inner cube. -/
theorem cat0_doubled_charts_agree_of_auxiliaries (hX : IsCAT0 X)
    {f g : EuclideanSpace ℝ ι → X}
    (hf : ∀ x ∈ coordinateCube ι 2, ∀ y ∈ coordinateCube ι 2, dist (f x) (f y) = dist x y)
    (hg : ∀ x ∈ coordinateCube ι 2, ∀ y ∈ coordinateCube ι 2, dist (g x) (g y) = dist x y)
    (hc : f 0 = g 0)
    (ho : ∀ z ∈ coordinateCubeCorners ι 1, ∃ o : X, dist (f 0) o ≤ ‖z‖ ∧
      dist (f ((2 : ℝ) • z)) o ≤ ‖z‖ ∧ dist (g ((2 : ℝ) • z)) o ≤ ‖z‖) :
    (coordinateCube ι 1).EqOn f g := by
  apply cat0_doubled_charts_agree hX hf hg
  intro z hz
  have hz₁ : z ∈ coordinateCube ι 1 := by
    rw [← convexHull_coordinateCubeCorners (zero_le_one' ℝ)]
    exact subset_convexHull _ _ hz
  have hz₂ := interior_subset (coordinateCube_one_subset_interior_two hz₁)
  have h0 : (0 : EuclideanSpace ℝ ι) ∈ coordinateCube ι 2 := fun _ ↦ by constructor <;> norm_num
  have h2z : (2 : ℝ) • z ∈ coordinateCube ι 2 := by
    intro j
    change -2 ≤ 2 * z j ∧ 2 * z j ≤ 2
    exact ⟨by linarith [(hz₁ j).1], by linarith [(hz₁ j).2]⟩
  obtain ⟨o, hcenter, hfo, hgo⟩ := ho z hz
  have identify {k : EuclideanSpace ℝ ι → X}
      (hk : ∀ x ∈ coordinateCube ι 2, ∀ y ∈ coordinateCube ι 2, dist (k x) (k y) = dist x y)
      (hko : dist (k 0) o ≤ ‖z‖) (hzo : dist (k ((2 : ℝ) • z)) o ≤ ‖z‖) : k z = o := by
    apply (cat0_auxiliary_midpoint hX (a := k 0) (b := k ((2 : ℝ) • z))
      (by rw [hk _ h0 _ h2z, dist_zero_left, norm_smul]; norm_num) hko hzo).2.2
    · rw [hk _ h0 _ hz₂, dist_zero_left]
    · rw [hk _ h2z _ hz₂, dist_eq_norm, two_smul, add_sub_cancel_right]
  exact (identify hf hcenter hfo).trans (identify hg (hc ▸ hcenter) hgo).symm

end Cubes

end SpectralBooks
end LinearAlgebra
end OAI
