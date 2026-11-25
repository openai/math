import OAI.Computability.BorderVNP.PackedSeedBoxRate
import OAI.Computability.BorderVNP.DiagonalExternalSewResourceScale

/-!
# Sewn record budgets at the actual seed description and channel widths

The private one-copy payload includes the whole opaque padded description.
The sparse initial count uses only public names. One admissible processor
exponent controls both charges and all outer histories.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover CoverScale TeamScales Filter Diagonal.ExternalSew
open scoped Classical

/-- Specializing the two sewn resource estimates to the true finite-cover
width and complete one-copy private descriptor, with integral copy, epoch and
cell thresholds. The fixed bound A may include the direction catalog and
the native per-record constants. -/
theorem eventually_seed_sewn_caps {α τ : ℝ} (hα : 0 < α) (hα' : α < 1/1000) (hτ : 0 < τ)
    (ht : τ < α/100) {fan C : ℕ} (hfan : 1 ≤ fan) (hc : 1 ≤ C)
    (fanGrowth : τ*Real.logb 2 fan ≤ α) (growth : τ*Real.logb 2 C ≤ α/10)
    (q degree headerFactor A : ℕ) [NeZero q] :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n:ℝ)^ω) →
      ∀ depth, depth+1 = initialDepth (Fin q) r n →
      let H := seedChannelWidth n r q depth
      let cap := seedBoxCapacity n r q depth degree
      let dB := seedDescriptionWidth n r q depth (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
      let b := width n α
      let T := epochs τ n
      ∀ BP BE : ℕ, BP ≤ A*b → BE ≤ A*b*(1+H+dB) →
        5*b*(C^T*BP) ≤ width n (1/100) ∧ 7*(C^T*BE) ≤ width n (1/5) ∧ BE ≤ width n (1/5) := by
  obtain ⟨u,hu,hw⟩ := eventually_seed_capacity q hτ
  obtain ⟨v,B,hv,hB,htape⟩ := eventually_padded_seed_description hα hα' hτ ht q degree headerFactor
  have hcr : 1 ≤ (C:ℝ) := by exact_mod_cast hc
  obtain ⟨z,hz,hbud⟩ := eventually_sewn_resources hα' hτ ht hfan fanGrowth hcr growth 4
  let A₁ := (96*(4*(q:ℝ)+1)+1)*factor (Fin q)
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  let A₂ := (A:ℝ)*(1+A₁+B)
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  refine ⟨min u (min v z),lt_min hu (lt_min hv hz),?_⟩
  filter_upwards [hw,htape,hbud A₂ hA₂,eventually_ge_atTop 1] with n hW hT hS hn
  intro r hr room depth level H cap dB b T BP BE hp he
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have mono (γ : ℝ) (hγ : min u (min v z) ≤ γ) : (r:ℝ) ≤ 2^((n:ℝ)^γ) :=
    room.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (Real.rpow_le_rpow_of_exponent_le hn' hγ))
  have hH := (hW r hr (mono u (min_le_left ..)) depth level).1
  have hdB := (hT r hr (mono v ((min_le_right ..).trans (min_le_left ..))) depth level).2.1
  let L := (logWidth r n:ℝ)
  let N := (n:ℝ)^(1/10+τ/20)
  have hL : 1 ≤ L := by
    have h := Nat.clog_mono_right 2 (show 2 ≤ 2*n*r by nlinarith)
    change 1 ≤ (logWidth r n:ℝ)
    rw [Shortening.PublicCapacity.public_logWidth n r]
    exact_mod_cast ((by decide : 1 ≤ Nat.clog 2 2).trans h)
  have hN : 1 ≤ N := Real.one_le_rpow hn' (by linarith)
  have hH' : (H:ℝ) ≤ A₁*N*L^4 := hH.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by decide : 3 ≤ 4)) (by positivity))
  have hdB' : (dB:ℝ) ≤ B*N*L^4 := hdB
  have hsum : (1+H+dB:ℝ) ≤ (1+A₁+B)*(N*L^4) := by
    have h₁ : 1 ≤ N*L^4 := one_le_mul_of_one_le_of_one_le hN (one_le_pow₀ hL)
    nlinarith only [hH',hdB',h₁]
  have hA : (A:ℝ) ≤ A₂ := le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  have pub : ((C^T*BP:ℕ):ℝ) ≤ A₂*(C:ℝ)^T*b := by
    push_cast
    have hp' : (BP:ℝ) ≤ A*b := by exact_mod_cast hp
    calc
      _ ≤ (C:ℝ)^T*(A₂*b) := mul_le_mul_of_nonneg_left (hp'.trans (mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg _))) (by positivity)
      _ = _ := by ring
  have mass : ((C^T*BE:ℕ):ℝ) ≤ A₂*(C:ℝ)^T*b*N*L^4 := by
    have he' : (BE:ℝ) ≤ A*b*(1+H+dB) := by exact_mod_cast he
    push_cast
    calc
      _ ≤ (C:ℝ)^T*((A:ℝ)*b*((1+A₁+B)*(N*L^4))) := by gcongr; exact he'.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = _ := by dsimp [A₂]; ring
  have h := hS r hr (mono z ((min_le_right ..).trans (min_le_right ..))) (C^T*BP) (C^T*BE) pub mass
  refine ⟨h.1,h.2,?_⟩
  have hpow : 0 < C^T := pow_pos (by omega) _
  exact ((Nat.le_mul_of_pos_left BE hpow).trans (Nat.le_mul_of_pos_left _ (by decide : 0<7))).trans h.2

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
