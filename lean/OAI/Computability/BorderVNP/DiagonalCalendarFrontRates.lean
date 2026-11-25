import OAI.Computability.BorderVNP.DiagonalFrozenCalendarWitness
import OAI.Computability.BorderVNP.DiagonalCommonRouteHeader
import OAI.Computability.BorderVNP.DiagonalBootedJointClock

/-! # Uniform route and header bounds on each selected calendar reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Epoch Packing Diagonal.ExternalSew PackedHistoryCircuit.Normalized
open Filter TeamScales TeamContraction ProcessorSlots RoutingISA RoutingISA.Evaluator.ScheduleClock
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar Cover

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} (cube : FixedCube K) {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    (b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1))
    (φ : K →+* F) (q : ℕ) {hm : 0 < m} {adv : ℕ → ℕ}

/-- The actual common-header width and the native path estimate for all readers of this batch. -/
def CalendarPrefixRatesAt (c charge n : ℕ) : Prop :=
  CoreAt scales.α ((scales.τ:ℝ)/5) n ∧
      ∀ {l : ℕ}, n=l+1 → ∀ {header C A₀ a B₀ b₀ J j coeff addr power cut factor : ℕ}
        (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))
        {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
        (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
          (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
          (adv (adviceScale b.σ b.ρ (l+1))+6))
        (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge),
        ((cal.frozenLayout chart reader chargeFit).header:ℝ) ≤ stretch b.ρ (l+1)*((l+1:ℕ):ℝ)^(24/25:ℝ)

set_option maxRecDepth 7000 in
set_option maxHeartbeats 500000 in
/-- One cutoff controls the true link header and the route evaluator for all physical
calendar readers at every later length. -/
theorem JointSchedule.eventually_calendar_prefix_rates (poly : PolynomiallyBounded adv) (c charge : ℕ) :
    ∀ᶠ n : ℕ in atTop, CalendarPrefixRatesAt cube b φ q (hm:=hm) (adv:=adv) c charge n := by
  have positive : 0 < (scales.α:ℝ) := by exact_mod_cast scales.alpha_pos
  have route := eventually_core_at (α:=(scales.α:ℝ)) (ξ:=(scales.τ:ℝ)/5) (by linarith [scales.tau_small])
  filter_upwards [route,b.eventually_common_route_header (aux:=φ ∘ cube.table) (q:=q) cube adv poly c charge] with n core fit
  unfold CalendarPrefixRatesAt
  refine ⟨core,?_⟩
  intro l eqn header C A₀ a B₀ b₀ J j coeff addr power cut factor cal ord common chart prime alg reader chargeFit
  subst n
  rw [(cal.frozenLayout_fields chart reader chargeFit).1]
  exact (fit.2 chart reader chargeFit).2.1

end Diagonal

end BorderVNP
end Computability
end OAI
