import OAI.Computability.VPVNP.Barycenter
import OAI.Computability.VPVNP.WireSpectrum
import Mathlib.Analysis.Real.Sqrt

/-! # Wire costs and the central advice source -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.WireTensor VPVNP.SpectralGeometry

/-- The supply-cost inequality for a restriction between products of binary wires. -/
theorem wire_cost_le {K J E P : Type} [Field K] [Fintype J] [Fintype E] [Fintype P]
    (F : SpectralPoint K J) (a b : E → J) (u v : P → J) (w : E → ℕ) (bits : P → ℕ)
    (restriction : Restricts (wireNetwork (k := K) a b (fun e => Fin (2 ^ w e)))
      (wireNetwork u v (fun p => Fin (2 ^ bits p)))) :
    ∑ p, (bits p : ℝ) * F.wireDistance (u p) (v p) ≤
      ∑ e, (w e : ℝ) * F.wireDistance (a e) (b e) := by
  have mono := NNReal.coe_le_coe.mpr (F.monotone restriction)
  rw [F.value_binary_wireNetwork, F.value_binary_wireNetwork] at mono
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp mono

/-- Averaging the CAT(0) variance inequality at a second independent draw. -/
theorem exists_center_half_energy {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    [CompleteSpace X] [Nonempty X] (segments : HasCATZeroSegments X)
    (mass : I → ℝ) (points : I → X) (nonneg : ∀ i, 0 ≤ mass i)
    (total : ∑ i, mass i = 1) :
    ∃ center : X, 2 * weightedSquaredDistance mass points center ≤
      ∑ j, mass j * weightedSquaredDistance mass points (points j) := by
  obtain ⟨center, variance⟩ := exists_barycenter_variance segments mass points nonneg total
  refine ⟨center, ?_⟩
  have bound := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    mul_le_mul_of_nonneg_left (variance (points j)) (nonneg j)
  simp_rw [mul_add, dist_comm center] at bound
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, total, one_mul] at bound
  simpa only [two_mul, weightedSquaredDistance] using bound

/-- The scalar variance estimate for distances to the center controls any
nonnegative advice weights, without requiring independence of their locations. -/
theorem central_cost {V : Type*} [Fintype V] (h radius : V → ℝ) (mean err : ℝ)
    (hn : ∀ v, 0 ≤ h v) (hm : mean ≤ 1 / Real.sqrt 2)
    (variance : ∑ v, (radius v - mean)^2 ≤ err) :
    ∑ v, h v * radius v ≤ (∑ v, h v) / Real.sqrt 2 +
      Real.sqrt (∑ v, (h v)^2) * Real.sqrt err := by
  have cs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ h (fun v => radius v - mean)
  simp_rw [mul_sub] at cs
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at cs
  have mu := mul_le_mul_of_nonneg_left hm (Finset.sum_nonneg (s := Finset.univ) fun v _ => hn v)
  have dev := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt variance)
    (Real.sqrt_nonneg (∑ v, (h v)^2))
  rw [mul_one_div] at mu
  linarith

private theorem sum_on_list {I V : Type*} [Fintype I] [Fintype V]
    (sites : I ↪ V) (cost : V → ℝ) (nonneg : ∀ v, 0 ≤ cost v) :
    ∑ i, cost (sites i) ≤ ∑ v, cost v := by
  classical
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => nonneg v)

/-- Restrict scalar variance estimates to independent uniform draws from two
terminal lists. Each list can contain every vertex from the other list.
Only one factor of P/N is lost on division by the number of terminal pairs. -/
theorem terminal_pair_deviation {V : Type*} [Fintype V] {N : ℕ} (left right : Fin N ↪ V)
    (d : V → V → ℝ) (g : V → ℝ) (μ err : ℝ)
    (columns : ∀ t, ∑ v, (d v t-g t)^2 ≤ err)
    (means : ∑ t, (g t-μ)^2 ≤ err) :
    (∑ j, ∑ i, (d (left i) (right j)-1)^2) ≤
      6*N*err + 3*(N:ℝ)^2*(μ-1)^2 := by
  have row (j : Fin N) : ∑ i, (d (left i) (right j)-g (right j))^2 ≤ err :=
    (sum_on_list left _ (fun _ => sq_nonneg _)).trans (columns (right j))
  have between : ∑ j, (g (right j)-μ)^2 ≤ err :=
    (sum_on_list right _ (fun _ => sq_nonneg _)).trans means
  have triple (a b c : ℝ) : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
    nlinarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]
  have each (j : Fin N) : (∑ i, (d (left i) (right j)-1)^2) ≤
      3*(err+N*(g (right j)-μ)^2+N*(μ-1)^2) := by
    have point (i : Fin N) := triple (d (left i) (right j)-g (right j)) (g (right j)-μ) (μ-1)
    simp only [sub_add_sub_cancel] at point
    have sum := Finset.sum_le_sum (s := Finset.univ) fun i _ => point i
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at sum
    linarith [row j]
  have all := Finset.sum_le_sum (s := Finset.univ) fun j _ => each j
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at all
  nlinarith only [all,mul_le_mul_of_nonneg_left between (Nat.cast_nonneg N)]

end OAI.Computability.MultitapeWeakETH
