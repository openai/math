import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialArrayTree
import OAI.Optimization.LinearProgramming.PriceGame.CampaignWeightCost

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Campaign

open TrialExecution Moment States.Mass Learning

/-- All prepared allocation rows charge their denominators to this same physical local-weight
grid, including the incoming values after fixed sharing. -/
theorem actual_localGrid_bound {N : ℕ} (anchor : Fin N) (R T : ℕ) (hT : T ≤ (N+R.size+1)^300)
    (out : ℕ → RoundResult N) (t : ℕ) (ht : t ≤ T)
    (obs : ∀ j < t, (out j).observations.length ≤ Pool.probeBudget N) :
    populationDenominator R out t * etaQ.den^probes ≤ 2^(registerWeightPolynomial.eval (N+R.size+1)) := by
  let a := catalogueBits N R T
  let D := populationDenominator R out t
  have hd : D ≤ 2^(a+(6+a)*T) := (populationDenominator_le R out t a
    (population_binary_at_prefix anchor R T out t ht obs)).trans
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left (6+a) ht) a))
  have hlocal := local_denominator_dyadic_bound D (a+(6+a)*T) probes probes hd
  rw [Nat.min_self] at hlocal
  have hcap : a+(6+a)*T+learningRateBits*probes ≤ campaignWeightBits N R T := by
    change a+(6+a)*T+learningRateBits*probes ≤ 3 + _ + 2*(a+(6+a)*T+learningRateBits*probes)
    exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans (Nat.le_add_left _ _)
  exact hlocal.trans (Nat.pow_le_pow_right (by decide) (hcap.trans (campaignWeightBits_polynomial N R T hT)))

private theorem share_width (n : ℕ) : 2*(3+4*n)+4 = 2*(3+2*(n+n))+4 := by omega

private theorem scalar_width (n : ℕ) : 2*n+4 ≤ 2*(3+4*n)+4 := by omega

private theorem local_unit_pos (D r : ℕ) (hd : 0 < D) : 0 < D*etaQ.den^r :=
  Nat.mul_pos hd (Nat.pow_pos etaQ.den_pos)

/-- Inputs and physical prepared arrays at every reachable child/prefix of a run started
from the actual shared campaign weights. The shape parameters of the envelope are public. -/
theorem prefix_trial_array_bounds (env : Control.Wire.Envelope) {N : ℕ} (anchor : Fin N) (R T : ℕ)
    (hT : T ≤ (N+R.size+1)^300) (ed : depth N ≤ env.depth) (ev : 2*N^2 ≤ env.vertices)
    (ee : ((N+R.size+1)*(T+1))^Pool.catalogueExponent ≤ env.experts)
    (ep : 2*trialPriceBits N (((N+R.size+1)*(T+1))^Pool.catalogueExponent) R Bits.commonDenominator
      +4 ≤ env.width)
    (ew : 2*(3+4*registerWeightPolynomial.eval (N+R.size+1))+4 ≤ env.width)
    (out : ℕ → RoundResult N) (t : ℕ) (ht : t≤T)
    (hs : ∀ j<t, PublicRoundBounds (population R out j) (out j)) :
    let p := population R out t
    env.TrialArraysFit probes R (populationExperts p) (depth N) 0 .root (fun _ _ => 0)
      (populationWeights p) p.nonnegative := by
  let p := population R out t
  let D := populationDenominator R out t
  let B := registerWeightPolynomial.eval (N+R.size+1)
  have obs j (hj : j<t) := (hs j hj).observations
  have count := population_length_at_prefix anchor R T out t ht obs
  have raw : RawBox Bits.commonDenominator R (populationExperts p) := by
    intro e i _
    apply Pool.catalogue_entry_grid (hist := seenProbes out) (T := t+1)
    rw [← population_entries]
    exact List.getElem_mem ..
  have dpos := local_unit_pos D probes (populationDenominator_pos anchor R out t)
  have eprice := (Nat.add_le_add_right (Nat.mul_le_mul_left 2
    (trialPriceBits_mono_experts N R Bits.commonDenominator count)) 4).trans ep
  change 2*(3+4*B)+4 ≤ env.width at ew
  apply env.trialArraysFit_of_registers probes R Bits.commonDenominator D (D*etaQ.den^probes) B B
    (populationExperts p) raw (Nat.zero_lt_of_lt anchor.isLt) probes_pos Bits.commonDenominator_pos
    dpos (actual_localGrid_bound anchor R T hT out t ht obs) ed ev (count.trans ee) eprice
    ((scalar_width B).trans ew) ((share_width B) ▸ ew) (depth N) 0 (Nat.zero_add _).le .root (fun _ _ => 0)
    (populationWeights p) p.nonnegative (fun _ _ _ => rfl) True.intro (fun _ hj => (Nat.not_lt_zero _ hj).elim)
  exact prefix_weight_registers_polynomial anchor R T hT out t ht hs

/-- Every history-dependent run satisfies the prefix conditions for these arrays. -/
theorem actual_trial_array_bounds (env : Control.Wire.Envelope) {N : ℕ} (anchor : Fin N) (R T : ℕ)
    (hT : T ≤ (N+R.size+1)^300) (ed : depth N ≤ env.depth) (ev : 2*N^2 ≤ env.vertices)
    (ee : ((N+R.size+1)*(T+1))^Pool.catalogueExponent ≤ env.experts)
    (ep : 2*trialPriceBits N (((N+R.size+1)*(T+1))^Pool.catalogueExponent) R Bits.commonDenominator
      +4 ≤ env.width)
    (ew : 2*(3+4*registerWeightPolynomial.eval (N+R.size+1))+4 ≤ env.width)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool))
    (out : ℕ → RoundResult N)
    (hx : ∀ j : Fin T, out j.val = ((trialLoop (Pool.batch N R)
      (runRound R (fun experts => marketSolverAtCommonWeightUnit experts))
      T (Population.start (Pool.batch N R))).run reply history) j)
    (t : ℕ) (ht : t ≤ T) :
    let p := population R out t
    env.TrialArraysFit probes R (populationExperts p) (depth N) 0 .root (fun _ _ => 0)
      (populationWeights p) p.nonnegative :=
  prefix_trial_array_bounds env anchor R T hT ed ev ee ep ew out t ht (fun j hj =>
    (all_replay_bounds anchor R T (fun es => marketSolverAtCommonWeightUnit es)).run reply history out hx j (hj.trans_le ht))

end Campaign
end PriceGame
end LinearProgramming
end Optimization
end OAI
