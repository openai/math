import OAI.Computability.BorderVNP.TeamScales

/-!
# Numerical room for the cube balancing and packet schedule

The alphabet ceiling, the fixed packet block, and the sparse list operations
in Section 8 use the same `n` as the processor scales in Section 7. The
bounds below are eventual in `n`, uniformly for the multiplicities in the paper.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

open Filter

/-- The alphabet size in Section 8.1. -/
noncomputable def alphabet (α : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (3*α)⌉₊

/-- The number of full product labels. -/
noncomputable def labelCount (α : ℝ) (a n : ℕ) : ℕ := (alphabet α n)^a

/-- Any fixed power of the product-label count fits the prescribed exponent
with a small allowance for the alphabet rounding. -/
theorem eventually_labelCount_power {α : ℝ} (hα : 0 < α) (a k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (labelCount α a n : ℝ)^k ≤ (n : ℝ)^(4*α*a*k) := by
  filter_upwards [TeamScales.eventually_rpow_gap (show 3*α < 4*α by linarith) 2,
    eventually_ge_atTop 1] with n hg hn
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have h1 : 1 ≤ (n:ℝ)^(3*α) := Real.one_le_rpow hn' (by positivity)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (n:ℝ)^(3*α) by positivity)
  have h : (alphabet α n : ℝ) ≤ (n:ℝ)^(4*α) := by unfold alphabet; linarith
  calc
    _ ≤ (((n:ℝ)^(4*α))^a)^k := by unfold labelCount; push_cast; gcongr
    _ = _ := by
      rw [← Real.rpow_natCast _ a, ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast _ k, ← Real.rpow_mul (by positivity)]

/-- The explicit variance estimate fits the squared slack in Lemma 8.2,
uniformly for every larger total volume and every smaller cell incidence cap. -/
theorem eventually_balancing_slack {α ξ : ℝ} (hα : 0 < α) (a : ℕ)
    (hgap : 24*α*a + 1/4 < 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ (W M : ℝ), (n:ℝ)^(1-ξ)/2 ≤ W →
      0 ≤ M → M ≤ (n:ℝ)^(1/4 : ℝ) →
      let Z : ℝ := labelCount α a n
      Z^2*(4*W*M) + Z*(W*M) ≤ (W/Z^2)^2 := by
  filter_upwards [eventually_labelCount_power hα a 6, TeamScales.eventually_rpow_gap hgap 10,
    eventually_ge_atTop 1] with n hZ hg hn
  intro W M hW hM hMn Z
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have ha : 1 ≤ alphabet α n := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn' _)
  have hone : 1 ≤ Z := by change (1 : ℝ) ≤ ((alphabet α n)^a : ℕ); exact_mod_cast one_le_pow₀ ha
  have hzp : 0 < Z := zero_lt_one.trans_le hone
  have hw0 : 0 ≤ W := (by positivity : 0 ≤ (n:ℝ)^(1-ξ)/2).trans hW
  have hcombined : 5*Z^6*M ≤ W := by
    have h1 : 10*Z^6*M ≤ (n:ℝ)^(1-ξ) := by
      apply le_trans _ hg
      calc
        _ ≤ 10*((n:ℝ)^(4*α*a*(6:ℕ)))*(n:ℝ)^(1/4 : ℝ) := by gcongr
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hn']; congr 2; push_cast; ring
    linarith only [h1,hW]
  have h5 : Z^5 ≤ Z^6 := pow_le_pow_right₀ hone (by decide)
  have hM5 := mul_le_mul_of_nonneg_right h5 hM
  have hc : (4*Z^6*M + Z^5*M)*W ≤ W*W :=
    mul_le_mul_of_nonneg_right (by linarith only [hcombined,hM5]) hw0
  rw [div_pow]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [hc]

/-- The sparse work expression in Lemma 8.2 includes two descriptor factors,
ten label factors, and a `polylog(nr)` budget bounded by `n^γ`. -/
theorem eventually_balancing_work {α γ : ℝ} (hα : 0 < α) (a : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hgap : 9/10 + 2/100 + 40*α*a + γ < 95/100) :
    ∀ᶠ n : ℕ in atTop, ∀ (r V H : ℝ), 0 ≤ r → 0 ≤ V → V ≤ K*r*(n:ℝ)^(9/10 : ℝ) →
      0 ≤ H → H ≤ (n:ℝ)^γ →
      V*(n:ℝ)^(2/100 : ℝ)*(labelCount α a n : ℝ)^10*H < r*(n:ℝ)^(95/100 : ℝ) ∨ r = 0 := by
  filter_upwards [eventually_labelCount_power hα a 10,
    TeamScales.eventually_rpow_gap hgap (K+1), eventually_ge_atTop 1] with n hZ hg hn
  intro r V H hr hV hVK hH hHn
  rcases hr.eq_or_lt with hr0 | hr0
  · exact Or.inr hr0.symm
  left
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  let e := (9/10 + 2/100 + 40*α*a + γ : ℝ)
  calc
    _ ≤ (K*r*(n:ℝ)^(9/10 : ℝ))*(n:ℝ)^(2/100 : ℝ)*
        (n:ℝ)^(4*α*a*(10:ℕ))*(n:ℝ)^γ := by gcongr
    _ = r*(K*(n:ℝ)^e) := by
      have he : e = 9/10 + 2/100 + 4*α*a*(10:ℕ) + γ := by dsimp [e]; ring
      rw [he, Real.rpow_add hn', Real.rpow_add hn', Real.rpow_add hn']; ring
    _ < r*((K+1)*(n:ℝ)^e) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right (lt_add_one K) (Real.rpow_pos_of_pos hn' _)) hr0
    _ ≤ _ := mul_le_mul_of_nonneg_left hg hr

end Cube

end BorderVNP
end Computability
end OAI
