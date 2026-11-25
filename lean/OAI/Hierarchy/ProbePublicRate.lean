import OAI.Hierarchy.ProbeStockRemainder

namespace OAI
/-! # A single native batch rate for all word lengths, populations and scheduled times -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section
universe v

/-- The ledger divisor is `K*B` when the native fixed counter uses one batch size
for packets whose maximum width is B. A single choice of K pays both the curvature
and all positive-demand debits, even at the smallest auxiliary replay time. -/
theorem uniform_packet_rate {a s₀ ρ γ C L : ℝ} {B multiplicity : ℕ}
    (ha : 0<a) (hs₀ : 0<s₀) (hρ : 0<ρ) (hγ : 0<γ) (hC : 0≤C) (_hL : 0≤L) (hB : 0<B) :
    ∃ K₀ : ℕ, 0<K₀ ∧ ∀ K≥K₀, ∀ s : ℝ, s₀≤s →
      (multiplicity:ℝ)/K ≤ s*a*γ ∧
      ∀ (I : Type v) [Fintype I] (n : ℕ) (δ : I→ℝ),
      (Fintype.card I:ℝ) ≤ L*n → (∀i, |δ i|≤C/K) →
      (∑ i, (δ i)^2/(4*s*a)) ≤ (n:ℝ)*ρ*γ/(8*(K*B:ℕ)) := by
  have bp : 0<(B:ℝ) := by exact_mod_cast hB
  let stock := (multiplicity:ℝ)/(s₀*a*γ)
  let curve := 2*L*C^2*B/(s₀*a*ρ*γ)
  obtain ⟨K₀,huge⟩ := exists_nat_gt (max 0 (max stock curve))
  have kp : 0<(K₀:ℝ) := lt_of_le_of_lt (le_max_left ..) huge
  refine ⟨K₀,by exact_mod_cast kp,?_⟩
  intro K big s time
  have rise : (K₀:ℝ)≤K := by exact_mod_cast big
  have Kpos := kp.trans_le rise
  have spos := hs₀.trans_le time
  have raw : stock≤K := (le_max_left stock curve).trans ((le_max_right ..).trans (huge.le.trans rise))
  have cnt := (div_le_iff₀ (show 0<s₀*a*γ by positivity)).mp raw
  have reserve := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right time ha.le) hγ.le
  refine ⟨(div_le_iff₀ Kpos).mpr (by nlinarith only [cnt,mul_le_mul_of_nonneg_left reserve Kpos.le]),?_⟩
  intro I _ n δ dim row
  have rawCurve : curve≤K := (le_max_right stock curve).trans ((le_max_right ..).trans (huge.le.trans rise))
  have funded := (div_le_iff₀ (show 0<s₀*a*ρ*γ by positivity)).mp rawCurve
  have energy (i : I) : (δ i)^2/(4*s*a) ≤ (C/K)^2/(4*s₀*a) := by
    have sq : (δ i)^2 ≤ (C/K)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg hC Kpos.le)).mpr (row i)
    apply (div_le_div_of_nonneg_right sq (show 0≤4*s*a by positivity)).trans
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left time (by norm_num)) ha.le
  calc
    _ ≤ ∑ _ : I,(C/K)^2/(4*s₀*a) := Finset.sum_le_sum fun i _ => energy i
    _ = (Fintype.card I:ℝ)*((C/K)^2/(4*s₀*a)) := by simp
    _ ≤ (L*n)*((C/K)^2/(4*s₀*a)) := mul_le_mul_of_nonneg_right dim (by positivity)
    _ ≤ _ := by
      rw [Nat.cast_mul]
      apply (le_div_iff₀ (by positivity : 0<8*((K:ℝ)*B))).2
      have base : L*((C/K)^2/(4*s₀*a))*(8*(K*B)) ≤ ρ*γ := by
        field_simp [Kpos.ne',hs₀.ne',ha.ne']
        nlinarith only [funded]
      nlinarith only [mul_le_mul_of_nonneg_left base (Nat.cast_nonneg (α:=ℝ) n)]

end
end Hierarchy.AdaptiveProbe

end OAI
