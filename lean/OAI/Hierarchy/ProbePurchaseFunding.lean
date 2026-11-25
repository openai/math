import OAI.Hierarchy.ProbePurchaseScale
import OAI.Hierarchy.ProbeAdvisedCost

namespace OAI
/-! # The actual fee of each acquired CT probe is paid by its signed movement -/

namespace Hierarchy.AdaptiveProbe
open ProbeStage Filter
open scoped BigOperators Classical
noncomputable section

/-- Units on a genuine selected path, all in unnormalized one-payload-bit prices.
The width-zero link pays only this activation fee prior to any later installation. -/
theorem fee_affordable {W k N T fee : ℝ} (wpos : 0<W) (kpos : 0<k) (npos : 0<N) (tpos : 0<T)
    (cheap : 64*k*fee*W^4*N≤1) : fee ≤ (W⁻¹^4/(N*T^2)*(T^2/(4*k))/8)/2 := by
  rw [per_chain_reward wpos npos tpos kpos]
  apply (le_div_iff₀ (by norm_num : 0<(2:ℝ))).2
  apply (le_div_iff₀ (show 0<32*k*N by positivity)).2
  rw [inv_pow,← one_div]; apply (le_div_iff₀ (pow_pos wpos 4)).2
  nlinarith only [cheap]

/-- Supply the exact fixed price and density requested by `strict_activation`
from the measured socket count, without a further scale/payment premise. -/
theorem advised_fee {p σ Λ : ℝ} (hp : 1<p) (hσ : 0<σ) (hΛ : 0<Λ) (k : ℕ) (hk : 0<k) :
    ∀ᶠ W : ℕ in atTop, ∀ h : ℕ, ∀ π : Equiv.Perm (Fin (2^h)),
    let t := dyadicScale W
    let T := t^2
    let N := (advisedRoute h (2^W) π).layers.length
    let H := ⌈32*(k:ℝ)/T⌉₊
    let u : ℝ := T^2/(4*(k:ℝ))
    let ρ : ℝ := u*(N:ℝ)/(2*(H:ℝ))
    let B : ℝ := (W:ℝ)⁻¹^4/((N:ℝ)*T^2)
    0<ρ ∧ 0<B ∧ 0<u ∧ Λ*t^p ≤ (B*u/8)/2 := by
  filter_upwards [affordable_advised hp hσ hΛ (by norm_num : (0:ℝ)<1/4) k,Filter.eventually_ge_atTop 1] with W charges large
  intro h π
  let N := (advisedRoute h (2^W) π).layers.length
  have nk : 0<N := by dsimp [N]; rw [advised_length]; omega
  have posN : (0:ℝ)<N := by exact_mod_cast nk
  have kw : (0:ℝ)<k := by exact_mod_cast hk
  have ww : (0:ℝ)<W := by exact_mod_cast large
  have posT : (0:ℝ)<(dyadicScale W)^2 := by dsimp [dyadicScale]; positivity
  have HH : (0:ℕ)<⌈32*(k:ℝ)/(dyadicScale W)^2⌉₊ := Nat.ceil_pos.mpr (by positivity)
  refine ⟨by positivity,by positivity,by positivity,?_⟩
  apply fee_affordable ww kw posN posT
  convert (charges h π).2.2.1 using 1; ring

end
end Hierarchy.AdaptiveProbe

end OAI
