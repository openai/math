import OAI.ThreeFlat.BoundedCrossing
import OAI.ThreeFlat.CrossingData

namespace OAI
/-! # Escape of the two horizontal endpoints

In a normalized sequence violating the crossing estimate the path excess at each
site tends to zero. The positive slack in the side matching forces both endpoint
distances to grow at least linearly in the penalty on path excess.
-/

namespace ThreeFlat

open Filter HyperbolicObstruction
open scoped Topology BigOperators

private theorem endpoint_growth_bound {X : Type*} [MetricSpace X] (hX : CATZero X)
    (A B : X) (x : Fin 4 → X) {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ)
    (hd : ∀ i, dist (x 0) (x i) ≤ 1)
    (he : ∀ i, dist A (x i) + dist B (x i) - dist A B ≤ 2/r)
    (hgap : τ + phaseCorr (fun i ↦ dist A (x i) - dist B (x i)) <
      xDemand (fun i j ↦ dist (x i) (x j))) :
    τ^2 * r < 64 * (dist (x 0) A + 1) := by
  let M := dist (x 0) A + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hxi (i : Fin 4) : dist A (x i) ≤ M := by
    dsimp [M]
    rw [dist_comm (x 0) A]
    linarith [dist_triangle A (x 0) (x i), hd i]
  have pair (i j : Fin 4) :=
    dist_le_phase_of_near_segment hX A B (x i) (x j) (hxi i) (hxi j) (he i) (he j)
  have hgap' : τ < 4 * Real.sqrt (2*M*(2/r)) := by
    simp only [xDemand, phaseCorr] at hgap
    linarith [pair 0 2, pair 1 3]
  have hs := (sq_lt_sq₀ hτ.le (by positivity)).mpr hgap'
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hs
  have heq : (4:ℝ)^2 * (2*M*(2/r)) = (64*M)/r := by ring
  rw [heq] at hs
  exact (lt_div_iff₀ hr).mp hs

private theorem tendsto_atTop_of_endpoint_growth (f : ℕ → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hg : ∀ n : ℕ, τ^2 * ((n : ℝ)+1) < 64*(f n+1)) : Tendsto f atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt ((64*(b+1))/τ^2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNb := (div_lt_iff₀ (sq_pos_of_pos hτ)).mp hN
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith [mul_le_mul_of_nonneg_right hn' (sq_nonneg τ), hg n, sq_nonneg τ]

/-- The marked points in a violating sequence have vanishing excess and the
two endpoint sequences escape their pointed balls. -/
theorem crossing_escape {X : ℕ → Type*} [∀ n, MetricSpace (X n)]
    (hX : ∀ n, CATZero (X n)) (A B : ∀ n, X n) (x : ∀ n, Fin 4 → X n)
    {τ : ℝ} (hτ : 0 < τ)
    (hnorm : ∀ n, xMass (fun i j ↦ dist (x n i) (x n j)) = 1)
    (hbad : ∀ n : ℕ, xSide (fun i j ↦ dist (x n i) (x n j)) + τ +
        phaseCorr (fun i ↦ dist (A n) (x n i) - dist (B n) (x n i)) +
        ((n : ℝ)+1) * ∑ i, (dist (A n) (x n i) + dist (B n) (x n i) - dist (A n) (B n))
        < xDemand (fun i j ↦ dist (x n i) (x n j))) :
    (∀ i : Fin 4, Tendsto (fun n ↦
      dist (A n) (x n i) + dist (B n) (x n i) - dist (A n) (B n)) atTop (𝓝 0)) ∧
      Tendsto (fun n ↦ dist (x n 0) (A n)) atTop atTop ∧
      Tendsto (fun n ↦ dist (x n 0) (B n)) atTop atTop := by
  let e (n : ℕ) (i : Fin 4) := dist (A n) (x n i) + dist (B n) (x n i) - dist (A n) (B n)
  let b (n : ℕ) (i : Fin 4) := dist (A n) (x n i) - dist (B n) (x n i)
  let d (n : ℕ) (i j : Fin 4) := dist (x n i) (x n j)
  have hviolate (n : ℕ) : xSide (d n) + τ + phaseCorr (b n) + ((n:ℝ)+1) * ∑ i, e n i <
      xDemand (d n) := hbad n
  have he0 (n : ℕ) (i : Fin 4) : 0 ≤ e n i := by
    dsimp [e]
    linarith [dist_triangle_right (A n) (B n) (x n i)]
  have hsum (n : ℕ) : 0 ≤ ∑ i, e n i := Finset.sum_nonneg fun i _ ↦ he0 n i
  have hd (n : ℕ) (i j : Fin 4) : d n i j ≤ 1 :=
    (le_xMass (d := d n) (fun _ _ ↦ dist_nonneg) i j).trans_eq (hnorm n)
  have hs (n : ℕ) : 0 ≤ xSide (d n) :=
    (add_nonneg dist_nonneg dist_nonneg).trans (le_max_left _ _)
  have hp (n : ℕ) : 0 ≤ phaseCorr (b n) := by unfold phaseCorr; positivity
  have hsmall (n : ℕ) (i : Fin 4) : e n i ≤ 2/((n:ℝ)+1) := by
    have hr : 0 < ((n:ℝ)+1) := by positivity
    have htotal := Finset.single_le_sum (fun j _ ↦ he0 n j) (Finset.mem_univ i)
    apply (le_div_iff₀ hr).mpr
    have h := hviolate n
    unfold xDemand at h
    linarith [mul_le_mul_of_nonneg_left htotal hr.le, hd n 0 2, hd n 1 3, hs n, hp n]
  have hm (n : ℕ) : τ + phaseCorr (b n) < xDemand (d n) := by
    linarith [hviolate n, hs n, mul_nonneg (by positivity : 0 ≤ (n:ℝ)+1) (hsum n)]
  refine ⟨fun i ↦ squeeze_zero (fun n ↦ he0 n i) (fun n ↦ hsmall n i) ?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  · apply tendsto_atTop_of_endpoint_growth _ hτ
    exact fun n ↦ endpoint_growth_bound (hX n) (A n) (B n) (x n) (by positivity)
      hτ (hd n 0) (hsmall n) (hm n)
  · apply tendsto_atTop_of_endpoint_growth _ hτ
    intro n
    apply endpoint_growth_bound (hX n) (B n) (A n) (x n) (by positivity) hτ (hd n 0)
    · intro i
      dsimp [e] at hsmall
      rw [add_comm, dist_comm (B n) (A n)]
      exact hsmall n i
    · have hphase : phaseCorr (fun i ↦ dist (B n) (x n i) - dist (A n) (x n i)) =
          phaseCorr (b n) := by
        simp only [phaseCorr, b]
        rw [show dist (B n) (x n 0) - dist (A n) (x n 0) -
              (dist (B n) (x n 2) - dist (A n) (x n 2)) = -(b n 0 - b n 2) by dsimp [b]; ring,
            show dist (B n) (x n 1) - dist (A n) (x n 1) -
              (dist (B n) (x n 3) - dist (A n) (x n 3)) = -(b n 1 - b n 3) by dsimp [b]; ring,
            abs_neg, abs_neg]
      rw [hphase]
      exact hm n

end ThreeFlat

end OAI
