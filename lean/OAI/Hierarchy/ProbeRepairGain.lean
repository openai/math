import Mathlib.Tactic

namespace OAI
/-! # The decrease shared by the two executed repair branches -/

namespace Hierarchy.AdaptiveProbe.OuterBank

/-- The per-site decrease is common to every outgoing choice. The purchase
uses half its certified divergence margin to pay all mesh and rounding costs. -/
noncomputable def repairGain (K : ℕ) (ρ γ ρBuy reward : ℝ) : ℝ :=
  min (ρ*γ/(8*K)) (ρBuy*reward/8)

theorem repairGain_pos {K : ℕ} {ρ γ ρBuy reward : ℝ} (hK : 0<K)
    (hρ : 0<ρ) (hγ : 0<γ) (hρBuy : 0<ρBuy) (hr : 0<reward) :
    0 < repairGain K ρ γ ρBuy reward :=
  lt_min (by positivity) (by positivity)

end Hierarchy.AdaptiveProbe.OuterBank

end OAI
