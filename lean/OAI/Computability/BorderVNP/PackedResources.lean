import OAI.Computability.BorderVNP.PackedPotential

/-! # Local storage and public traversal budgets of Proposition 7.2

A bottom bundle holds `⌊n^α⌋` copies at identical positions. The local size is allowed to grow
by `C` per epoch, but the public reconstruction traverses descriptors rather than individual
bit slots. The estimates below distinguish these two measures and keep the team size uniform.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open TeamScales Filter

private theorem epoch_le_logWidth {τ : ℝ} (hτ : 0 ≤ τ) (hτ' : τ ≤ 1) {n r : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) : (epochs τ n : ℝ) ≤ logWidth r n := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hl := Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hn'
  calc
    _ ≤ τ * Real.logb 2 n := Nat.floor_le (mul_nonneg hτ hl)
    _ ≤ 1 * Real.logb 2 n := mul_le_mul_of_nonneg_right hτ' hl
    _ ≤ Real.logb 2 (2 * (n : ℝ) * r) := by
      rw [one_mul]
      apply (Real.logb_le_logb (by norm_num) (zero_lt_one.trans_le hn') (by positivity)).mpr
      nlinarith
    _ ≤ _ := Nat.le_ceil _

/-- Cost per tile and reconstruction time in Proposition 7.2 (i)–(ii). The factor `n^(1/10+Δ)`
is the scale `s/V`. All fixed constants implicit in local routing, the site count, and the growth
of retained histories can be absorbed in `A`. The same choice of `ω` works for every `A`. -/
theorem eventually_sparse_resources_below {α τ C : ℝ} {K : ℕ}
    (hα' : α < 1 / 1000) (hτ : 0 < τ) (hτ' : τ < α / 100)
    (hK : 1 ≤ K) (hteams : τ * Real.logb 2 K ≤ α) (hC : 1 ≤ C)
    (hgrowth : τ * Real.logb 2 C ≤ α / 10) (D : ℕ) (γ : ℝ)
    (hγ : 2*α + 9/10 + 1/100 + τ/2000 < γ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A →
      ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2 ^ ((n : ℝ) ^ ω) →
      let L := (logWidth r n : ℝ)
      let T := epochs τ n
      A * C ^ T * width n α * (n : ℝ) ^ (1 / 10 + τ / 20) * L ^ D ≤ width n (1 / 5) ∧
      A * C ^ T * width n α ≤ width n (1 / 100) ∧
      A * T * teams α τ K n * (r * (n : ℝ) ^ (9 / 10 : ℝ)) * (n : ℝ) ^ (1 / 100 : ℝ) *
        L ^ D < r * (n : ℝ) ^ γ := by
  obtain ⟨ω, hω, hpoly⟩ := exists_polylog_budget (D + 1) (show 0 < τ / 2000 by positivity)
  refine ⟨ω, hω, fun A hA => ?_⟩
  have hw := eventually_le_rounded_width
    (show α / 10 + α + (1 / 10 + τ / 20) + τ / 2000 < 1 / 5 by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) < 1) A
  have hd := eventually_le_rounded_width (show α / 10 + α < 1 / 100 by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) < 1) A
  have ht := VPVNP.Compression.eventually_absorb_polylog A 0
    hγ
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hw, hd, ht, hpoly, eventually_ge_atTop 2] with n hnw hnd hnt hp hn
  intro r hr hrmax
  dsimp only
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  let L := (logWidth r n : ℝ)
  have hL : 1 ≤ L := by
    have harg : 2 ≤ (2 * (n : ℝ) * r) := by
      have hn' : 2 ≤ (n : ℝ) := by exact_mod_cast hn
      have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    calc
      _ = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ _ := ((Real.logb_le_logb (by norm_num : 1 < (2 : ℝ)) (by norm_num) (by positivity)).mpr harg)
      _ ≤ _ := Nat.le_ceil _
  have hD : L ^ D ≤ (n : ℝ) ^ (τ / 2000) :=
    (pow_le_pow_right₀ hL (Nat.le_succ D)).trans (hp r hr hrmax)
  have he := epoch_growth_le hC hn1 hτ.le hgrowth
  have hb : (width n α : ℝ) ≤ (n : ℝ) ^ α := Nat.floor_le (Real.rpow_nonneg hn0.le _)
  have hpre : A * C ^ epochs τ n * width n α ≤ A * (n : ℝ) ^ (α / 10 + α) := by
    rw [Real.rpow_add hn0]
    calc
      _ ≤ A * (n : ℝ) ^ (α / 10) * (n : ℝ) ^ α := by gcongr
      _ = _ := by ring
  refine ⟨?_, hpre.trans (by simpa using hnd), ?_⟩
  · calc
      _ ≤ A * (n : ℝ) ^ (α / 10 + α) * (n : ℝ) ^ (1 / 10 + τ / 20) * (n : ℝ) ^ (τ / 2000) := by
        gcongr
      _ = A * (n : ℝ) ^ (α / 10 + α + (1 / 10 + τ / 20) + τ / 2000) := by
        rw [Real.rpow_add hn0 _ (τ / 2000), Real.rpow_add hn0 (α / 10 + α) _]; ring
      _ ≤ _ := by simpa using hnw
  · have hR := teams_le hK hn1 hτ.le hteams
    have hT := epoch_le_logWidth hτ.le (by linarith) hn1 hr
    have hTL : (epochs τ n : ℝ) * L ^ D ≤ (n : ℝ) ^ (τ / 2000) := by
      calc
        _ ≤ L * L ^ D := mul_le_mul_of_nonneg_right hT (by dsimp [L]; positivity)
        _ = L ^ (D + 1) := (pow_succ' L D).symm
        _ ≤ _ := hp r hr hrmax
    simp only [pow_zero, mul_one] at hnt
    calc
      _ = (r : ℝ) * (A * teams α τ K n * (n : ℝ) ^ (9 / 10 : ℝ) * (n : ℝ) ^ (1 / 100 : ℝ) *
          ((epochs τ n : ℝ) * L ^ D)) := by dsimp [L]; ring
      _ ≤ (r : ℝ) * (A * (n : ℝ) ^ (2 * α) * (n : ℝ) ^ (9 / 10 : ℝ) * (n : ℝ) ^ (1 / 100 : ℝ) *
          (n : ℝ) ^ (τ / 2000)) := by gcongr
      _ = (r : ℝ) * (A * (n : ℝ) ^ (2 * α + 9 / 10 + 1 / 100 + τ / 2000)) := by
        rw [Real.rpow_add hn0 _ (τ / 2000), Real.rpow_add hn0 _ (1 / 100), Real.rpow_add hn0 _ (9 / 10)]; ring
      _ ≤ (r : ℝ) * (1 / 2 * (n : ℝ) ^ γ) := mul_le_mul_of_nonneg_left hnt hr0.le
      _ < _ := by nlinarith [mul_pos hr0 (Real.rpow_pos_of_pos hn0 γ)]

/-- The paper's public traversal exponent for the same expanded and sparse bounds. -/
theorem eventually_sparse_resources {α τ C : ℝ} {K : ℕ}
    (hα' : α < 1 / 1000) (hτ : 0 < τ) (hτ' : τ < α / 100)
    (hK : 1 ≤ K) (hteams : τ * Real.logb 2 K ≤ α) (hC : 1 ≤ C)
    (hgrowth : τ * Real.logb 2 C ≤ α / 10) (D : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A →
      ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2 ^ ((n : ℝ) ^ ω) →
      let L := (logWidth r n : ℝ)
      let T := epochs τ n
      A * C ^ T * width n α * (n : ℝ) ^ (1 / 10 + τ / 20) * L ^ D ≤ width n (1 / 5) ∧
      A * C ^ T * width n α ≤ width n (1 / 100) ∧
      A * T * teams α τ K n * (r * (n : ℝ) ^ (9 / 10 : ℝ)) * (n : ℝ) ^ (1 / 100 : ℝ) *
        L ^ D < r * (n : ℝ) ^ (93 / 100 : ℝ) :=
  eventually_sparse_resources_below hα' hτ hτ' hK hteams hC hgrowth D (93/100) (by linarith)

end Packing

end BorderVNP
end Computability
end OAI
