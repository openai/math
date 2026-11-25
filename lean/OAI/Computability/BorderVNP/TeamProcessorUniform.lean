import OAI.Computability.BorderVNP.TeamProcessorInstallation

/-!
# One admissible exponent for every quantitative team-simulation condition

Fix the word power and all logarithmic degrees first. Choose a single positive
exponent for the real team count which simultaneously pays for the actual
interior wiring in little-o scale, the processor's whole measured computation,
and the requested logarithmic overhead allowance.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open TeamScales Wires Filter

private theorem eventually_port_ratio (D : ℕ) {ξ : ℝ} (hξ : 0 < ξ) (hsmall : ξ < 3) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ reg c : ℕ, ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams →
      (teams : ℝ) ≤ (2 : ℝ)^((n : ℝ)^ω) →
      let w := logWidth teams n^D
      c*innerWidth teams reg w (sortExponent (block ξ n)) (w+1) ≤ n := by
  obtain ⟨ω,hω,cap⟩ := eventually_sorting_links (D+2) hξ
  refine ⟨ω,hω,fun reg c => ?_⟩
  filter_upwards [cap (c*(2*reg+686)),eventually_ge_atTop 1] with n hc hn
  intro teams ht bound w
  have H : 0 < block ξ n := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow (by exact_mod_cast hn : 1 ≤ (n : ℝ))
      (show 0 ≤ 1-ξ/3 by linarith)
  exact (Nat.mul_le_mul_left c (innerWidth_bound ht hn H reg D)).trans
    (by simpa only [Nat.mul_assoc] using hc teams ht bound)

/-- Uniform quantitative installation at the full processor range of §§7.1–7.2.
The logarithmic allowance `γ` can be `Δ/100`. The arbitrary constant multiple
in the second conjunct expresses the physical per-site interior port count as
`o(n)` uniformly in the team size. The third conjunct constructs the actual
word/register/clock geometry and verifies the physical path clock. -/
theorem uniform_installation (D logDegree : ℕ) {α ξ γ : ℝ} (hα : α < 3)
    (hξ : 0 < ξ) (hsmall : ξ < 3/2) (horder : ξ ≤ α) (hγ : 0 < γ) :
    ∃ ω : ℝ, 0 < ω ∧
      (∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams → (teams : ℝ) ≤ (2 : ℝ)^((n : ℝ)^ω) →
        (logWidth teams n : ℝ)^logDegree ≤ (n : ℝ)^γ) ∧
      (∀ reg c : ℕ, ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams → (teams : ℝ) ≤ (2 : ℝ)^((n : ℝ)^ω) →
        let w := logWidth teams n^(D+1)
        c*innerWidth teams reg w (sortExponent (block ξ n)) (w+1) ≤ n) ∧
      (∀ {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
        (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g),
        ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, 0 < teams → (teams : ℝ) ≤ (2 : ℝ)^((n : ℝ)^ω) →
        ∀ other : ℕ, ∃ geo : SiteGeometry P lib α ξ teams n other (logWidth teams n^(D+1))
          (sortExponent (block ξ n)), geo.measured) := by
  obtain ⟨u,hu,logs⟩ := exists_polylog_budget logDegree hγ
  obtain ⟨v,hv,ports⟩ := eventually_port_ratio (D+1) hξ (by linarith)
  obtain ⟨z,hz,measured⟩ := eventually_measured_sites D hα hξ hsmall horder
  let ω := min u (min v z)
  refine ⟨ω,lt_min hu (lt_min hv hz),?_,?_,?_⟩
  · filter_upwards [logs,eventually_ge_atTop 1] with n cap hn
    intro teams ht bound
    exact cap teams ht (admissible_smaller hn (min_le_left ..) bound)
  · intro reg c
    filter_upwards [ports reg c,eventually_ge_atTop 1] with n cap hn
    intro teams ht bound
    exact cap teams ht (admissible_smaller hn ((min_le_right ..).trans (min_le_left ..)) bound)
  · intro pc reg k routines m g Q Γ inst P lib
    filter_upwards [measured P lib,eventually_ge_atTop 1] with n cap hn
    intro teams ht bound
    exact cap teams ht (admissible_smaller hn ((min_le_right ..).trans (min_le_right ..)) bound)

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
