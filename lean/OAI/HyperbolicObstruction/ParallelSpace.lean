import OAI.HyperbolicObstruction.ParallelLines

namespace OAI
/-! # The transverse space of calibrated parallel lines

Intersect the family of parallel lines with the zero level of their common
unit-speed coordinate. Interpolating two calibrated lines at each time gives
another calibrated line. This proves the CAT(0) comparison on the transverse
space and recovers the isometric Euclidean product with a line.
-/

namespace HyperbolicObstruction.CATZero

variable {X : Type*} [MetricSpace X]

/-- A synchronously parametrized line in the bounded-distance class of `r`. -/
structure Calibrated (b : X → ℝ) (r l : ℝ → X) : Prop where
  isometry : Isometry l
  coordinate : ∀ t, b (l t) = t
  bounded : ∃ C : ℝ, ∀ t, dist (l t) (r t) ≤ C

namespace Calibrated

variable {b : X → ℝ} {r l m : ℝ → X}

theorem bounded_pair (hl : Calibrated b r l) (hm : Calibrated b r m) :
    ∃ C : ℝ, ∀ t, dist (l t) (m t) ≤ C := by
  obtain ⟨A, hA⟩ := hl.bounded
  obtain ⟨B, hB⟩ := hm.bounded
  exact ⟨A + B, fun t ↦ (dist_triangle_right _ _ _).trans (add_le_add (hA t) (hB t))⟩

/-- Pythagoras for two lines at possibly different levels. -/
theorem dist_sq (hl : Calibrated b r l) (hm : Calibrated b r m) (hX : CATZero X)
    (hb : LipschitzWith 1 b) (s t : ℝ) :
    dist (l s) (m t) ^ 2 = dist (l 0) (m 0) ^ 2 + (s - t) ^ 2 := by
  simpa using dist_sq_parallel_lines hX hl.isometry hm.isometry (hl.bounded_pair hm) hb
    (bx := 0) (by' := 0) (fun s ↦ by simp [hl.coordinate]) (fun t ↦ by simp [hm.coordinate]) s t

private theorem eq_of_dist_sq_bound {a t C : ℝ}
    (h : ∀ u : ℝ, (a - u) ^ 2 ≤ (t - u) ^ 2 + C ^ 2) : a = t := by
  by_contra hn
  let v := (C ^ 2 + 1) / (a - t)
  have hv : v * (a - t) = C ^ 2 + 1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hn)
  have h₁ := h (t - v)
  nlinarith [sq_nonneg (a - t), sq_nonneg C]

/-- Fixed-fraction interpolants of synchronized lines are themselves synchronized lines. -/
theorem interpolate (hl : Calibrated b r l) (hm : Calibrated b r m) (hX : CATZero X)
    (hb : LipschitzWith 1 b) {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    Calibrated b r (fun t ↦ segment hX (l t) (m t) θ) := by
  let p (t : ℝ) := segment hX (l t) (m t) θ
  let D := dist (l 0) (m 0)
  have hd (s t : ℝ) : dist (l s) (m t) ^ 2 = D ^ 2 + (s - t) ^ 2 :=
    hl.dist_sq hm hX hb s t
  have hsame (t : ℝ) : dist (l t) (m t) ^ 2 = D ^ 2 := by simpa using hd t t
  have hleft (s t : ℝ) : dist (l s) (p t) ^ 2 ≤ (s - t) ^ 2 + (θ * D) ^ 2 := by
    have h := segment_cn hX (l t) (m t) (l s) hθ
    rw [hl.isometry.dist_eq, Real.dist_eq, sq_abs, hd s t, hsame t] at h
    dsimp [p]
    convert h using 1
    ring
  have hright (s t : ℝ) :
      dist (m s) (p t) ^ 2 ≤ (s - t) ^ 2 + ((1 - θ) * D) ^ 2 := by
    have h := segment_cn hX (l t) (m t) (m s) hθ
    rw [dist_comm (m s) (l t), hd t s, hm.isometry.dist_eq, Real.dist_eq, sq_abs, hsame t] at h
    dsimp [p]
    convert h using 1
    ring
  have hcal (t : ℝ) : b (p t) = t := by
    apply eq_of_dist_sq_bound (C := θ * D)
    intro u
    have h := hb.dist_le_mul (p t) (l u)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, hl.coordinate] at h
    rw [dist_comm] at h
    have hs := (sq_le_sq₀ (abs_nonneg _) dist_nonneg).2 h
    rw [sq_abs] at hs
    nlinarith [hleft u t]
  refine ⟨Isometry.of_dist_eq (fun s t ↦ ?_), hcal, ?_⟩
  · have h := segment_cn hX (l t) (m t) (p s) hθ
    change dist (p s) (p t) ^ 2 ≤ _ at h
    rw [dist_comm (p s) (l t), dist_comm (p s) (m t), hsame t] at h
    have h₁ := mul_le_mul_of_nonneg_left (hleft t s) (sub_nonneg.mpr hθ.2)
    have h₂ := mul_le_mul_of_nonneg_left (hright t s) hθ.1
    have hc : dist (p s) (p t) ^ 2 ≤ (s - t) ^ 2 := by nlinarith
    have hlower := hb.dist_le_mul (p s) (p t)
    simp only [NNReal.coe_one, one_mul, hcal] at hlower
    apply le_antisymm _ hlower
    apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
    simpa [Real.dist_eq, sq_abs] using hc
  · obtain ⟨C, hC⟩ := hl.bounded
    refine ⟨θ * D + C, fun t ↦ (dist_triangle (p t) (l t) (r t)).trans ?_⟩
    apply add_le_add _ (hC t)
    rw [dist_comm, show dist (l t) (p t) = θ * dist (l t) (m t) from segment_left hX _ _ hθ]
    exact le_of_eq (congrArg (θ * ·) ((sq_eq_sq₀ dist_nonneg dist_nonneg).mp (hsame t)))

/-- Translate the origin of a line so its parameter agrees with the common coordinate. -/
theorem shift_to_zero {c : ℝ} (hl : Isometry l) (hc : ∀ t, b (l t) = t + c)
    (hp : ∃ C : ℝ, ∀ t, dist (l t) (r t) ≤ C) :
    Calibrated b r (fun t ↦ l (t - c)) := by
  obtain ⟨C, hC⟩ := hp
  refine ⟨Isometry.of_dist_eq (fun s t ↦ ?_), (fun t ↦ by simp [hc]), ⟨|c| + C, fun t ↦ ?_⟩⟩
  · rw [hl.dist_eq, Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_right]
  · apply (dist_triangle (l (t-c)) (l t) (r t)).trans
    rw [hl.dist_eq, Real.dist_eq, show t - c - t = -c by ring, abs_neg]
    exact add_le_add le_rfl (hC t)

end Calibrated

/-- The points on calibrated lines at parameter zero, with the ambient metric. -/
def Transverse (b : X → ℝ) (r : ℝ → X) :=
  {y : X // ∃ l : ℝ → X, Calibrated b r l ∧ l 0 = y}

namespace Transverse

variable {b : X → ℝ} {r : ℝ → X}

instance : MetricSpace (Transverse b r) := inferInstanceAs (MetricSpace (Subtype _))

noncomputable def line (y : Transverse b r) : ℝ → X := y.property.choose

theorem calibrated (y : Transverse b r) : Calibrated b r (line y) := y.property.choose_spec.1

@[simp] theorem line_zero (y : Transverse b r) : line y 0 = y.val := y.property.choose_spec.2

/-- Inclusion of all the parameterized lines preserves Euclidean product distances. -/
theorem dist_line_sq (hX : CATZero X) (hb : LipschitzWith 1 b) (y z : Transverse b r) (s t : ℝ) :
    dist (line y s) (line z t) ^ 2 = dist y z ^ 2 + (s - t) ^ 2 := by
  change dist (line y s) (line z t) ^ 2 = dist y.val z.val ^ 2 + (s - t) ^ 2
  simpa only [line_zero] using (calibrated y).dist_sq (calibrated z) hX hb s t

/-- A synchronized line is determined by its point in the transverse space. -/
theorem line_eq (hX : CATZero X) (hb : LipschitzWith 1 b) {l : ℝ → X}
    (hl : Calibrated b r l) (y : Transverse b r) (hy : l 0 = y.val) : line y = l := by
  funext t
  apply dist_eq_zero.mp
  have h := (calibrated y).dist_sq hl hX hb t t
  rw [hy, line_zero] at h
  have hz : dist (line y t) (l t) ^ 2 = 0 := by simpa using h
  exact (sq_eq_zero_iff).mp hz

/-- All ambient CAT(0) segments between zero-level points remain in the transverse space. -/
theorem catZero (hX : CATZero X) (hb : LipschitzWith 1 b) : CATZero (Transverse b r) := by
  classical
  intro y z
  let seg := segment hX y.val z.val
  have hmem (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ∃ l : ℝ → X, Calibrated b r l ∧ l 0 = seg t := by
    exact ⟨_, (calibrated y).interpolate (calibrated z) hX hb ht, by simp [seg]⟩
  let γ (t : ℝ) : Transverse b r := if ht : t ∈ Set.Icc (0 : ℝ) 1 then ⟨seg t, hmem t ht⟩ else y
  have hv {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : (γ t).val = seg t := by simp [γ, ht]
  have hseg := segment_spec hX y.val z.val
  refine ⟨γ, ⟨Subtype.ext ((hv (by norm_num)).trans hseg.1),
    Subtype.ext ((hv (by norm_num)).trans hseg.2.1), ?_⟩, ?_⟩
  · intro s hs t ht
    change dist (γ s).val (γ t).val = _ * dist y.val z.val
    rw [hv hs, hv ht]
    exact hseg.2.2 s hs t ht
  · intro x t ht
    change dist x.val (γ t).val ^ 2 ≤ _
    rw [hv ht]
    exact segment_cn hX y.val z.val x.val ht

/-- The ambient product embedding in distance form. -/
theorem dist_line (hX : CATZero X) (hb : LipschitzWith 1 b) (s t : ℝ) (y z : Transverse b r) :
    dist (line y s) (line z t) = Real.sqrt (dist s t ^ 2 + dist y z ^ 2) := by
  rw [Real.dist_eq, sq_abs, add_comm, ← dist_line_sq hX hb, Real.sqrt_sq dist_nonneg]

/-- A marked point at parameter zero on the input line lies at its phase over the
transverse factor. -/
theorem exists_line_at_phase (hX : CATZero X) (hb : LipschitzWith 1 b)
    {l : ℝ → X} {c : ℝ} (hl : Isometry l) (hc : ∀ t, b (l t) = t + c)
    (hp : ∃ C : ℝ, ∀ t, dist (l t) (r t) ≤ C) :
    ∃ y : Transverse b r, line y c = l 0 := by
  have hn := Calibrated.shift_to_zero hl hc hp
  let y : Transverse b r := ⟨l (0 - c), _, hn, rfl⟩
  refine ⟨y, ?_⟩
  have he := line_eq hX hb hn y rfl
  rw [he]
  simp

end Transverse

universe u

/-- A family of marked calibrated parallel lines lies in a CAT(0) Euclidean
product, with the phase of each marked point given by its calibration. -/
theorem exists_parallel_product {X : Type u} [MetricSpace X] {ι : Type*} (hX : CATZero X)
    {b : X → ℝ} (hb : LipschitzWith 1 b) (l : ι → ℝ → X) (c : ι → ℝ) (r : ℝ → X)
    (hl : ∀ i, Isometry (l i)) (hc : ∀ i t, b (l i t) = c i + t)
    (hp : ∀ i, ∃ C : ℝ, ∀ t, dist (l i t) (r t) ≤ C) :
    ∃ (Y : Type u) (_ : MetricSpace Y), CATZero Y ∧ ∃ (e : ℝ → Y → X) (y : ι → Y),
      (∀ s t : ℝ, ∀ v w : Y, dist (e s v) (e t w) = Real.sqrt (dist s t ^ 2 + dist v w ^ 2)) ∧
        ∀ i, l i 0 = e (c i) (y i) := by
  choose y hy using fun i ↦ Transverse.exists_line_at_phase hX hb (hl i)
    (fun t ↦ (hc i t).trans (add_comm _ _)) (hp i)
  exact ⟨Transverse b r, inferInstance, Transverse.catZero hX hb,
    fun t v ↦ Transverse.line v t, y, Transverse.dist_line hX hb, fun i ↦ (hy i).symm⟩

end HyperbolicObstruction.CATZero

end OAI
