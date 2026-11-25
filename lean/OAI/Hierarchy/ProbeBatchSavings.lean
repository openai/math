import OAI.Hierarchy.ProbeStockRemainder

namespace OAI
/-! # Simultaneous savings from the integer histograms of the disjoint failed balls -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

variable {I R : Type*} [Fintype I] [Fintype R] {E : R → Type*} [∀ r, Fintype (E r)]

/-- The same histogram inequality applies on every native outgoing selector.
Its strict decrease is uniform in n and w after dividing the account by n. -/
theorem selected_histograms_drop {a M s ρ γ : ℝ} (b A z : I → ℝ)
    (kind : (Σ r, E r) → Option I) (installed consumed : (Σ r, E r) → ℕ)
    (weight : (Σ r, E r) → ℝ) (broadcast : R → ℝ) (width : R → ℕ)
    {K w n : ℕ} (ha : 0 < a) (hb : ∀ i, 0 ≤ b i) (hM : 0 ≤ M) (hs : 0 < s)
    (hz : ∀ i, 0 ≤ z i) (hA : ∀ i, 0 ≤ A i) (hw : 0 < w) (hK : 0 < K)
    (hγ : 0 < γ) (bw : ∀ r, 0 < width r) (wide : ∀ r, 2*(K*width r) ≤ w)
    (density : ρ*n ≤ Fintype.card R) :
    let unit := netUnits w installed consumed
    let δ := stockChange kind unit
    let x := maximizer a M s b A z
    let p := activePrice kind weight x
    (∀ i, 0 ≤ z i+δ i) →
    (∀ r, (∑ e, (installed ⟨r,e⟩:ℝ)*p ⟨r,e⟩)+broadcast r +
       (copied K (width r) w:ℝ)*(width r*γ/2) ≤ ∑ e, (consumed ⟨r,e⟩:ℝ)*p ⟨r,e⟩) →
    (∑ i, (δ i)^2/(4*s*a)) ≤ (n:ℝ)*ρ*γ/(8*K) →
    cashChange kind unit weight ((∑ r,broadcast r)/w) + potential a M s b A (fun i => z i+δ i)
      ≤ potential a M s b A z-(n:ℝ)*ρ*γ/(8*K) := by
  intro unit δ x p valid charged curvature
  let gain := fun r => (copied K (width r) w:ℝ)*(width r*γ/2)
  have combined := Finset.sum_le_sum (s:=Finset.univ) fun r _ => charged r
  simp only [Finset.sum_add_distrib] at combined
  have realW : 0 < (w:ℝ) := by exact_mod_cast hw
  have realK : 0 < (K:ℝ) := by exact_mod_cast hK
  have positive := (div_nonneg hγ.le (show 0 ≤ (2:ℝ) by norm_num))
  have per (r : R) : (w:ℝ)/(2*K)*(γ/2) ≤ gain r := by
    simpa only [gain,mul_div_assoc,←mul_assoc,mul_comm (width r:ℝ) (copied K (width r) w:ℝ)]
      using mul_le_mul_of_nonneg_right (copied_bits hK (bw r) (wide r)).1 positive
  have many := Finset.sum_le_sum (s:=Finset.univ) fun r _ => per r
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at many
  have supply := (mul_le_mul_of_nonneg_right density (show 0 ≤ (w:ℝ)/(2*K)*(γ/2) by positivity)).trans many
  have margin : (n:ℝ)*ρ*γ/(8*K) ≤ (∑ r, gain r)/(2*w) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(w:ℝ))).2
    convert supply using 1; ring
  have drop := histogram_drop (a:=a) (M:=M) (s:=s) b A z kind installed consumed weight hw
    (broadcast:=∑ r,broadcast r) (rawgain:=∑ r,gain r) ha hb hM hs hz hA valid
    (by simpa only [Fintype.sum_sigma,gain] using combined) (curvature.trans margin)
  exact drop.trans (sub_le_sub_left margin _)

end
end Hierarchy.AdaptiveProbe

end OAI
