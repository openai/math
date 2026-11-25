import OAI.LinearAlgebra.FiniteFourier.PackedWidthCost
import OAI.LinearAlgebra.FiniteFourier.PackedParameters

/-! # From the two local prime-axis constructions to integral open descent -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter Real

/-- The local circuit conclusion at two. The order contains the supplied
ternary radices and all nonscalar orbit lengths. -/
def AtTwoPackedCircuits (β C : ℝ) : Prop :=
  ∀ (n B M : ℕ) (P : Finset ℕ) (A : PrimeJetPacking P n M.totient B),
    0 < n → 6 ≤ B → Odd M → (∀ k : ℕ, 3^k ≤ 8*B → 3^k ∣ M) →
    (∀ p ∈ A.axes, p.Prime ∧ p ≤ B ∧ 7 ≤ p ∧ p % 4 = 3 ∧ (p-1)/2 ∣ M) →
    ProtectedPackedList n {2} (3*8*(9*n)) (A.childCutoff 8) (A.widthWork C β (A.childCutoff 8))

/-- The local circuit conclusion for the Gaussian binary kernel. The work
constant precedes the choice of all excluded primes. -/
def DyadicPackedCircuits (F : Type*) [Field F] (β C : ℝ) : Prop :=
  ∀ (η : ℝ) (n B : ℕ) (D : DyadicAxisPacking F η n B),
    0 < n → 6 ≤ B → ∀ L : Finset ℕ,
    (∀ l ∈ L, l.Prime ∧ l ≠ 2 ∧ ¬ l ∣ D.orderTimesVolume) →
    ProtectedPackedList n L (3*6*(9*n)) (D.packing.childCutoff 6)
      (D.packing.widthWork C β (D.packing.childCutoff 6))

/-- The packing and contraction parameters can be selected independently
of the gate-work estimate. At the chosen lengths the two local circuit
constructions give precisely the integer recurrence with coefficient 540. -/
theorem integralOpenDescent_of_packedCircuits {F : Type*} [Field F] [CharZero F]
    {β γ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβγ : β < γ) (hγ : γ ≤ 1) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (ha : AtTwoPackedCircuits β C₀) (hd : DyadicPackedCircuits F β C₁) :
    IntegralOpenDescent γ := by
  obtain ⟨σ, hσ, hσ', hpack⟩ := eventually_protectedPackings F
  refine ⟨σ, hσ, hσ', 162*(C₀+2*C₁)+4, by positivity, ?_⟩
  have ht := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpack, ht.eventually_ge_atTop 3, eventually_gt_atTop (0:ℕ),
    eventually_widthWork_le hβ hβγ hγ] with n ⟨d⟩ hT hn hwork
  change 3 ≤ log (n:ℝ) at hT
  let a := d.atTwo.childCutoff 8
  let b := d.first.packing.childCutoff 6
  let c := d.second.packing.childCutoff 6
  let s := max a (max b c)
  have ha' : a ≤ s := le_max_left ..
  have hb' : b ≤ s := (le_max_left ..).trans (le_max_right ..)
  have hc' : c ≤ s := (le_max_right ..).trans (le_max_right ..)
  have hapos : 0 < a := d.atTwo.childCutoff_pos hn (by decide)
  have hbpos : 0 < b := d.first.packing.childCutoff_pos hn (by decide)
  have hcpos : 0 < c := d.second.packing.childCutoff_pos hn (by decide)
  obtain ⟨B, hB, len, p, hp, hlen, hvol, hcost⟩ := assembleProtectedPackedLists
    d.second.orderTimesVolume_pos d.separate
    (ha n d.B₀ d.M d.P d.atTwo hn d.width₀ d.order_odd d.three_dvd d.axis_spec)
    (hd d.η n d.B d.first hn d.width) (hd d.η n d.B d.second hn d.width)
  let _ := hB
  refine ⟨s, B, hB, len, p, hapos.trans_le ha', d.short, hlen, hvol, hp, ?_⟩
  let W := convolutionGauge γ (log n) + (log (log n))^3 * convolutionEnvelope s
  have hx : (1:ℝ) ≤ d.B₀ := by exact_mod_cast (by have := d.width₀; omega : 1 ≤ d.B₀)
  have hy : (1:ℝ) ≤ d.B := by exact_mod_cast (by have := d.width; omega : 1 ≤ d.B)
  have h₀ := hwork d.atTwo hC₀ hx d.cutoff₀ hapos ha'
  have h₁ := hwork d.first.packing hC₁ hy d.cutoff hbpos hb'
  have h₂ := hwork d.second.packing hC₁ hy d.cutoff hcpos hc'
  have hone : 1 ≤ W := by
    have hlog := log_nonneg (by linarith : 1 ≤ log (n:ℝ))
    have henv := convolutionEnvelope_one_le (hapos.trans_le ha')
    exact (convolutionGauge_one_le (hβ.trans hβγ.le) hγ _).trans (le_add_of_nonneg_right (by positivity))
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  change (p.linearCost : ℝ)/n ≤ (162*(C₀+2*C₁)+4)*W
  apply (div_le_iff₀ hn').mpr
  change (p.linearCost : ℝ) ≤ d.atTwo.widthWork C₀ β a + d.first.packing.widthWork C₁ β b +
    d.second.packing.widthWork C₁ β c + 4*n at hcost
  change _ ≤ 162*C₀*n*W at h₀
  change _ ≤ 162*C₁*n*W at h₁ h₂
  have h₄ : 4*(n:ℝ) ≤ 4*n*W := le_mul_of_one_le_right (by positivity) hone
  linarith only [hcost, h₀, h₁, h₂, h₄]

end FiniteFourier
end LinearAlgebra
end OAI
