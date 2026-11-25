import OAI.Hierarchy.ProbeMaskedRoute
import OAI.Hierarchy.ProbeParameters

namespace OAI
/-! # Capacity at the actual dyadic CT stage count -/

namespace Hierarchy.AdaptiveProbe
open ProbeStage Filter Topology
noncomputable section

theorem advised_length (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) :
    (advisedRoute h d π).layers.length=18*(d-1)+1 := by
  have same := (Routes.layer_shapes (advisedRoute h d π)).trans (permutation_layout h d π).symm
  have len : (advisedRoute h d π).layers.length=(permutationRoute h d π).layers.length := by
    simpa only [List.length_map] using congrArg List.length same
  exact len.trans (permutation_stages h d π)

/-- A single dyadic choice works for all public permutations and all h. It pays
the exact per-stage tile charge for every signed layer and bounds the purchased probe
unit at its 1/64 saving margin. -/
theorem affordable_advised {p σ Λ τ : ℝ} (hp : 1 < p) (hσ : 0 < σ) (hΛ : 0 < Λ)
    (hτ : 0 < τ) (k : ℕ) : ∀ᶠ W : ℕ in atTop,
    ∀ h : ℕ, ∀ π : Equiv.Perm (Fin (2^h)), let t := dyadicScale W
      let N := (advisedRoute h (2^W) π).layers.length
      Λ*t^σ ≤ 1 ∧ Λ*(1+2*k)*(N:ℝ)*t^p ≤ 1 ∧
      64*k*Λ*(W:ℝ)^4*(N:ℝ)*t^p ≤ 1 ∧ (N:ℝ)*t^2 ≤ τ := by
  let K := Λ*(1+64*k)
  have pos : 0 < K := by dsimp [K]; positivity
  have hw := affordable_scale (p:=p) (σ:=σ) (C:=18) (K:=K) (τ:=τ) hp hσ (by norm_num) pos hτ
  filter_upwards [hw,eventually_ge_atTop 1] with W use one
  intro h π t N
  have tpos : 0 < t := by dsimp [t,dyadicScale]; positivity
  have scale : (2:ℝ)^W*t=1 := by dsimp [t,dyadicScale]; rw [←mul_pow]; norm_num
  have powpos : 0 < 2^W := by positivity
  have bound : N ≤ 18*2^W := by dsimp [N]; rw [advised_length]; omega
  have bound' : (N:ℝ) ≤ 18*(2:ℝ)^W := by exact_mod_cast bound
  have Nt : (N:ℝ)*t ≤ 18 := calc
    _ ≤ (18*(2:ℝ)^W)*t := mul_le_mul_of_nonneg_right bound' tpos.le
    _ = 18 := by rw [mul_assoc,scale,mul_one]
  obtain ⟨fee,all⟩ := use
  obtain ⟨cost,small⟩ := all N (Nat.cast_nonneg _) Nt
  have cheap : Λ ≤ K := by dsimp [K]; nlinarith only [mul_nonneg hΛ.le (Nat.cast_nonneg (α:=ℝ) k)]
  have layer : Λ*(1+2*k) ≤ K := by dsimp [K]; nlinarith only [mul_nonneg hΛ.le (Nat.cast_nonneg (α:=ℝ) k)]
  have buy : 64*k*Λ ≤ K := by dsimp [K]; nlinarith only [hΛ.le]
  have realW : 1 ≤ (W:ℝ) := by exact_mod_cast one
  have grow : 1≤(W:ℝ)^4 := one_le_pow₀ realW
  have bigger : K ≤ K*(W:ℝ)^4 := by simpa using mul_le_mul_of_nonneg_left grow pos.le
  refine ⟨(mul_le_mul_of_nonneg_right cheap (Real.rpow_nonneg tpos.le _)).trans fee,?_,?_,small⟩
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (layer.trans bigger)
      (Nat.cast_nonneg N)) (Real.rpow_nonneg tpos.le _)).trans cost
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right buy (by positivity)) (Nat.cast_nonneg N)) (Real.rpow_nonneg tpos.le _)).trans cost

end
end Hierarchy.AdaptiveProbe

end OAI
