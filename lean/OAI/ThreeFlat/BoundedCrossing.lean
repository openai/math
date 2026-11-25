import OAI.Geometry.HyperbolicGroups.CATZero

namespace OAI
/-! # A crossing with a bounded endpoint

A small broken-path excess locates each of the four sites close to a
single segment whenever its distance from one endpoint is bounded. The
distance along that segment is half the difference of the phases.
-/

namespace ThreeFlat

open HyperbolicObstruction

variable {X : Type*} [MetricSpace X]

/-- Write the longitudinal coordinate as a fraction of the distance from
`A` to `B`. The assertion also covers a segment of length zero. -/
private theorem exists_phase_parameter (A B x : X) :
    ∃ u ∈ Set.Icc (0 : ℝ) 1,
      u * dist A B = (dist A B + (dist A x - dist B x)) / 2 := by
  by_cases h : A = B
  · subst B
    exact ⟨0, by simp, by simp⟩
  have hD := dist_pos.mpr h
  have h1 := dist_triangle B A x
  rw [dist_comm B A] at h1
  have h2 := dist_triangle A B x
  refine ⟨((dist A B + (dist A x - dist B x)) / 2) / dist A B, ⟨?_, ?_⟩,
    div_mul_cancel₀ _ hD.ne'⟩
  · exact div_nonneg (by linarith) hD.le
  · apply (div_le_one hD).mpr
    linarith

/-- A Euclidean comparison triangle bounds the transverse error by the
square root of twice the product of the endpoint distance and the excess. -/
private theorem dist_phase_projection_le (h : CATZero X) (A B x : X) {u M ε : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (huD : u * dist A B = (dist A B + (dist A x - dist B x)) / 2)
    (hr : dist A x ≤ M) (he : dist A x + dist B x - dist A B ≤ ε) :
    dist x (CATZero.segment h A B u) ≤ Real.sqrt (2 * M * ε) := by
  let δ := (dist A x + dist B x - dist A B) / 2
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    linarith [dist_triangle_right A B x]
  have hxA : dist x A = u * dist A B + δ := by
    dsimp [δ]
    rw [dist_comm x A]
    linarith
  have hxB : dist x B = (1-u) * dist A B + δ := by
    dsimp [δ]
    rw [dist_comm x B]
    linarith
  have hcn := CATZero.segment_cn h A B x hu
  rw [hxA, hxB] at hcn
  have hs : dist x (CATZero.segment h A B u) ^ 2 ≤ 2 * dist A x * (2 * δ) := by
    rw [← dist_comm x A, hxA]
    calc
      _ ≤ _ := hcn
      _ = 2 * (u * dist A B + δ) * (2 * δ) - (4 * u ^ 2 * dist A B * δ + 3 * δ ^ 2) := by ring
      _ ≤ _ := sub_le_self _ (by positivity)
  have hprod := mul_le_mul hr (show 2 * δ ≤ ε by dsimp [δ]; linarith)
    (by positivity : 0 ≤ 2 * δ) (dist_nonneg.trans hr)
  apply Real.le_sqrt_of_sq_le
  linarith only [hs, hprod]

/-- Two sites on short-excess paths from `A` to `B` pay for their mutual
distance with the phase difference and the two transverse errors. -/
theorem dist_le_phase_of_near_segment (h : CATZero X) (A B x y : X) {M ε : ℝ}
    (hx : dist A x ≤ M) (hy : dist A y ≤ M)
    (hex : dist A x + dist B x - dist A B ≤ ε)
    (hey : dist A y + dist B y - dist A B ≤ ε) :
    dist x y ≤ |(dist A x - dist B x) - (dist A y - dist B y)| / 2 +
      2 * Real.sqrt (2 * M * ε) := by
  obtain ⟨u, hu, huD⟩ := exists_phase_parameter A B x
  obtain ⟨v, hv, hvD⟩ := exists_phase_parameter A B y
  let c := CATZero.segment h A B
  have hcx := dist_phase_projection_le h A B x hu huD hx hex
  have hcy := dist_phase_projection_le h A B y hv hvD hy hey
  have hd := (CATZero.segment_spec h A B).2.2 u hu v hv
  have huv : (u - v) * dist A B =
      ((dist A x - dist B x) - (dist A y - dist B y)) / 2 := by
    rw [sub_mul, huD, hvD]
    ring
  rw [← abs_of_nonneg (dist_nonneg : 0 ≤ dist A B), ← abs_mul, huv, abs_div] at hd
  norm_num at hd
  change dist (c u) (c v) = _ at hd
  change dist x (c u) ≤ _ at hcx
  change dist y (c v) ≤ _ at hcy
  rw [dist_comm y (c v)] at hcy
  linarith [dist_triangle x (c u) y, dist_triangle (c u) (c v) y]

/-- Four sites with phases in `[lo,hi]` obey the bounded-endpoint part
of the catalytic crossing estimate. -/
theorem bounded_endpoint_crossing (h : CATZero X) (A B : X) (x : Fin 4 → X)
    {M ε lo hi : ℝ} (hr : ∀ i, dist A (x i) ≤ M)
    (he : ∀ i, dist A (x i) + dist B (x i) - dist A B ≤ ε)
    (hlo : ∀ i, lo ≤ dist A (x i) - dist B (x i))
    (hhi : ∀ i, dist A (x i) - dist B (x i) ≤ hi) :
    dist (x 0) (x 2) + dist (x 1) (x 3) ≤ hi - lo + 4 * Real.sqrt (2 * M * ε) := by
  have hb (i j : Fin 4) :
      |(dist A (x i) - dist B (x i)) - (dist A (x j) - dist B (x j))| ≤ hi - lo :=
    abs_le.mpr ⟨by linarith [hlo i, hhi j], by linarith [hhi i, hlo j]⟩
  have h02 := dist_le_phase_of_near_segment h A B (x 0) (x 2) (hr 0) (hr 2) (he 0) (he 2)
  have h13 := dist_le_phase_of_near_segment h A B (x 1) (x 3) (hr 1) (hr 3) (he 1) (he 3)
  linarith [hb 0 2, hb 1 3]

end ThreeFlat

end OAI
