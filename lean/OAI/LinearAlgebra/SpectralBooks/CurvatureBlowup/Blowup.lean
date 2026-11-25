import OAI.LinearAlgebra.SpectralBooks.Book.BookBlowup
import OAI.Geometry.HyperbolicGroups.IndexedFillingValue

/-!
# Infinitesimal rays of a Busemann convex space

The rescalings at the common source of finitely many segments all use the
same ultrafilter. On the resulting rays the equal-parameter distances are
linear, with slopes given by the infima of the original distance ratios.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace CurvatureBlowup

open HyperbolicObstruction Filter Topology Set

variable {X : Type*} [MetricSpace X]

/-- The original scale corresponding to magnification by `n + 1`. -/
def scale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

abbrev ultrafilter := Ultrafilter.of (atTop : Filter ℕ)
abbrev Space (o : X) := Book.Blowup ultrafilter scale_pos o
abbrev Section (o : X) := Book.BlowupSection ultrafilter scale_pos o

private theorem tendsto_parameter (r : ℝ) :
    Tendsto (fun n : ℕ ↦ r / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r

private theorem eventually_parameter {r : ℝ} (hr : 0 ≤ r) :
    ∀ᶠ n : ℕ in atTop, r / ((n : ℝ) + 1) ∈ Icc 0 1 := by
  filter_upwards [(tendsto_parameter r).eventually_lt_const zero_lt_one] with n hn
  exact ⟨div_nonneg hr (by positivity), hn.le⟩

private def sectionOf {o x : X} {a : ℝ → X} (ha : IsSegment a o x) (r : ℝ) : Section o where
  val n := ⟨if r / ((n : ℝ) + 1) ∈ Icc (0 : ℝ) 1 then a (r / ((n : ℝ) + 1)) else o⟩
  bound := by
    refine ⟨max 0 r * dist o x, fun n ↦ ?_⟩
    rw [MetricScale.dist_eq]
    dsimp only
    split_ifs with hn
    · rw [ha.dist_from_source hn, scale, inv_inv, ← mul_assoc,
        mul_div_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
    · simp [mul_nonneg (le_max_left 0 r) dist_nonneg]

/-- The ray obtained by evaluating a segment at `r / (n+1)`. -/
def ray {o x : X} {a : ℝ → X} (ha : IsSegment a o x) (r : ℝ) : Space o :=
  MetricLimit.point (sectionOf ha r)

private theorem tendsto_dist {o x y : X} {a b : ℝ → X}
    (ha : IsSegment a o x) (hb : IsSegment b o y) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * dist (a (r / ((n : ℝ) + 1))) (b (t / ((n : ℝ) + 1))))
      (ultrafilter : Filter ℕ) (𝓝 (dist (ray ha r) (ray hb t))) := by
  apply (MetricLimit.tendsto_point_dist (sectionOf ha r) (sectionOf hb t)).congr'
  apply Filter.Eventually.filter_mono (Ultrafilter.of_le _)
  filter_upwards [eventually_parameter hr, eventually_parameter ht] with n hn hm
  change (scale n)⁻¹ * dist _ _ = _
  simp only [sectionOf, ite_eq_left hn, ite_eq_left hm, scale, inv_inv]

/-- All the rays based at one point have the same origin. -/
theorem ray_zero {o x y : X} {a b : ℝ → X} (ha : IsSegment a o x) (hb : IsSegment b o y) :
    ray ha 0 = ray hb 0 := by
  apply dist_eq_zero.mp
  apply tendsto_nhds_unique (tendsto_dist ha hb le_rfl le_rfl)
  simp only [zero_div, ha.1, hb.1, dist_self, mul_zero]
  exact tendsto_const_nhds

/-- The original segment speed is the constant speed of its limiting ray. -/
theorem dist_same {o x : X} {a : ℝ → X} (ha : IsSegment a o x) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) :
    dist (ray ha r) (ray ha t) = |r - t| * dist o x := by
  apply tendsto_nhds_unique (tendsto_dist ha ha hr ht)
  apply tendsto_const_nhds.congr'
  apply Filter.Eventually.filter_mono (Ultrafilter.of_le _)
  filter_upwards [eventually_parameter hr, eventually_parameter ht] with n hn hm
  rw [ha.2.2 _ hn _ hm, ← sub_div, abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1),
    ← mul_assoc, mul_div_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]

/-- Equal-time separation laws on original segments persist on the full rays,
including the law for the two opposite halves of a segment. -/
theorem dist_opposite {o x y : X} {a b : ℝ → X}
    (ha : IsSegment a o x) (hb : IsSegment b o y) {c : ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) 1, dist (a s) (b s) = s * c) {r : ℝ} (hr : 0 ≤ r) :
    dist (ray ha r) (ray hb r) = r * c := by
  apply tendsto_nhds_unique (tendsto_dist ha hb hr hr)
  apply tendsto_const_nhds.congr'
  apply Filter.Eventually.filter_mono (Ultrafilter.of_le _)
  filter_upwards [eventually_parameter hr] with n hn
  rw [h _ hn, ← mul_assoc, mul_div_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]

private theorem ratio_mono {o x y : X} {a b : ℝ → X} (hB : RadialBusemann X)
    (ha : IsSegment a o x) (hb : IsSegment b o y) :
    MonotoneOn (fun s ↦ dist (a s) (b s) / s) (Ioc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have rest {u : X} {d : ℝ → X} (hd : IsSegment d o u) :
      IsSegment (fun v ↦ d (v*t)) o (d t) := by
    simpa only [mul_zero, zero_add, hd.1] using
      hd.reparam (by norm_num : (0 : ℝ) ∈ Icc 0 1) ⟨ht.1.le, ht.2⟩
  have h := hB o (a t) (b t) _ _ (rest ha) (rest hb) (s / t)
    ⟨div_nonneg hs.1.le ht.1.le, (div_le_one ht.1).mpr hst⟩
  simp only [div_mul_cancel₀ _ ht.1.ne'] at h
  apply (div_le_div_iff₀ hs.1 ht.1).mpr
  calc
    _ ≤ (s / t * dist (a t) (b t)) * t := mul_le_mul_of_nonneg_right h ht.1.le
    _ = _ := by field_simp [ht.1.ne']

/-- The infinitesimal separation slope is bounded by every positive-time
quotient of the original segments. -/
theorem dist_pair {o x y : X} {a b : ℝ → X} (hB : RadialBusemann X)
    (ha : IsSegment a o x) (hb : IsSegment b o y) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ dist x y ∧
      (∀ s ∈ Ioc (0 : ℝ) 1, c ≤ dist (a s) (b s) / s) ∧
      ∀ r : ℝ, 0 ≤ r → dist (ray ha r) (ray hb r) = r * c := by
  let f (s : ℝ) := dist (a s) (b s) / s
  let S := f '' Ioc (0 : ℝ) 1
  have h1 : (1 : ℝ) ∈ Ioc 0 1 := ⟨zero_lt_one, le_rfl⟩
  have hmem {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) : f s ∈ S := mem_image_of_mem f hs
  have hne : S.Nonempty := ⟨_, hmem h1⟩
  have hlow : 0 ∈ lowerBounds S := by
    rintro _ ⟨s, hs, rfl⟩
    exact div_nonneg dist_nonneg hs.1.le
  have hinf {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) : sInf S ≤ f s :=
    csInf_le ⟨0, hlow⟩ (hmem hs)
  refine ⟨sInf S, le_csInf hne hlow, ?_, fun _ hs ↦ hinf hs, ?_⟩
  · simpa only [f, ha.2.1, hb.2.1, div_one] using hinf h1
  intro r hr
  rcases hr.eq_or_lt with rfl | hr
  · simp [ray_zero ha hb]
  have hp (n : ℕ) : 0 < r / ((n : ℝ) + 1) := div_pos hr (by positivity)
  have hev : ∀ᶠ n : ℕ in atTop, r / ((n : ℝ) + 1) ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [eventually_parameter hr.le] with n hn
    exact ⟨hp n, hn.2⟩
  have hf : Tendsto (fun n : ℕ ↦ f (r / ((n : ℝ) + 1))) atTop (𝓝 (sInf S)) := by
    apply tendsto_order.mpr
    constructor
    · intro l hl
      exact hev.mono (fun n hn ↦ hl.trans_le (hinf hn))
    · intro u hu
      obtain ⟨_, ⟨s, hs, rfl⟩, hsu⟩ := exists_lt_of_csInf_lt hne hu
      filter_upwards [hev, (tendsto_parameter r).eventually_lt_const hs.1] with n hn hns
      exact ((ratio_mono hB ha hb) hn hs hns.le).trans_lt hsu
  apply tendsto_nhds_unique (tendsto_dist ha hb hr.le hr.le)
  apply ((hf.const_mul r).mono_left (Ultrafilter.of_le _)).congr
  intro n
  dsimp [f]
  field_simp
end CurvatureBlowup

end

end SpectralBooks
end LinearAlgebra
end OAI
