import OAI.Hierarchy.ProbeDensity

namespace OAI
/-! # Detecting high excess on the payload paths

All estimates are finite. Exceptional paths enter with their exact cardinality,
so the bound survives normalized limits on changing stage layouts. -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

private theorem path_triangle {E : Type*} [SeminormedAddCommGroup E] (z : ℕ → E) (N : ℕ) :
    ‖z N - z 0‖ ≤ ∑ i ∈ Finset.range N, ‖z (i+1) - z i‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have tri := norm_add_le (z (N+1)-z N) (z N-z 0)
    rw [sub_add_sub_cancel] at tri
    linarith

/-- The quoted price of one legal path is controlled by its measured signed readings
in the path's common Euclidean frame. -/
theorem payload_path {k N : ℕ} (z : ℕ → EuclideanSpace ℝ (Fin k))
    (v : Fin N → EuclideanSpace ℝ (Fin k × Bool)) {η price : ℝ} (hη : 0 ≤ η)
    (ends : price ≤ η + ‖z N-z 0‖)
    (close : ∀ t : Fin N, ∀ j, |signedVector (z (t.1+1)-z t.1) j - v t j| ≤ η) :
    price ≤ η + N*(Real.sqrt (2*k)*η) + ∑ t, ‖v t‖ := by
  have h := path_triangle z N
  rw [← Fin.sum_univ_eq_sum_range] at h
  have tiles := Finset.sum_le_sum (s:=Finset.univ) fun (t : Fin N) _ =>
    tile_displacement (z (t.1+1)-z t.1) (v t) hη (close t)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at tiles
  linarith

/-- When the normalized quadratic statistic is at most one, the mean payload price
is bounded by the cost of the signed measurement and the exact exceptional density. -/
theorem payload_mass {P E : Type*} [Fintype P] [SeminormedAddCommGroup E]
    {N : ℕ} (v : P → Fin N → E) (price : P → ℝ) (bad : Finset P)
    {T bias cap : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ bias) (_hc : 0 ≤ cap)
    (bounded : ∀ p, price p ≤ cap)
    (good : ∀ p ∉ bad, price p ≤ bias + ∑ t, ‖v p t‖)
    (energy : ∑ p, ∑ t, ‖v p t‖^2 ≤ Fintype.card P * (N:ℝ) * T^2) :
    ∑ p, price p ≤ Fintype.card P*bias + Fintype.card P*(N:ℝ)*T + bad.card*cap := by
  classical
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (P × Fin N))
    (fun _ => (1:ℝ)) (fun r => ‖v r.1 r.2‖)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_mul,Fintype.sum_prod_type] at cs
  have score : ∑ p, ∑ t, ‖v p t‖ ≤ Fintype.card P*(N:ℝ)*T := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      _ ≤ _ := cs
      _ ≤ ((Fintype.card P:ℝ)*N) * ((Fintype.card P:ℝ)*N*T^2) :=
        mul_le_mul_of_nonneg_left energy (by positivity)
      _ = _ := by ring
  have row (p : P) : price p ≤ (bias + ∑ t, ‖v p t‖) + (if p ∈ bad then cap else 0) := by
    by_cases h : p ∈ bad
    · rw [ite_eq_left h]
      have sn : 0 ≤ ∑ t, ‖v p t‖ := by positivity
      linarith [bounded p]
    · simpa [h] using good p h
  have bound := Finset.sum_le_sum (s:=Finset.univ) fun p _ => row p
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Finset.sum_ite_mem,Finset.univ_inter] at bound
  linarith

/-- Markov's bound with the actual set of roots failing a fixed local test. -/
theorem exceptional_test_mass {R : Type*} [Fintype R] (disc : R → ℝ) (nonneg : ∀ r, 0 ≤ disc r)
    (ε : ℝ) : let bad := Finset.univ.filter (fun r => ε < disc r)
    bad.card*ε ≤ ∑ r, disc r := by
  classical
  let bad := Finset.univ.filter (fun r => ε < disc r)
  change (bad.card:ℝ)*ε ≤ _
  calc
    _ = ∑ _r ∈ bad, ε := by simp
    _ ≤ ∑ r ∈ bad, disc r := Finset.sum_le_sum fun r hr => (Finset.mem_filter.mp hr).2.le
    _ ≤ ∑ r, disc r := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun r _ _ => nonneg r)

end
end Hierarchy.AdaptiveProbe

end OAI
