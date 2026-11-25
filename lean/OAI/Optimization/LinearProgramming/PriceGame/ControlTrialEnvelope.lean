import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPopulation
import OAI.Optimization.LinearProgramming.PriceGame.TrialWireBound
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingGuard
import OAI.Optimization.LinearProgramming.PriceGame.CampaignWeightCost

/-! One explicit numeric envelope for every intermediate state of a campaign trial. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open States.Mass TrialExecution

noncomputable def campaignEnvelope (N R T : ℕ) : Envelope where
  depth := depth N
  vertices := 2*N^2
  experts := expertCount N R T
  width := (2*trialPriceBits N (expertCount N R T) R Learning.Bits.commonDenominator+4) + (2*(3+4*Campaign.registerWeightPolynomial.eval (N+R.size+1))+4)
  score := (2*N)^274
  logSize := (2*(N+1))^604

def totalTrialTicks (N : ℕ) : ℕ := 5*(2*N)^602+(2*(N+1))^605

private theorem prefix_log_cap (r k top cap : ℕ) (hk : k ≤ top) (hcap : (6*r+1)^top ≤ cap) :
    probeLogBound r k ≤ cap :=
  (probeLogBound_le r k).trans ((Nat.pow_le_pow_right (Nat.succ_pos (6*r)) hk).trans hcap)

attribute [local irreducible] Moment.probes

theorem envelope_log_limit (N R T k : ℕ) (hk : k ≤ depth N) :
    probeLogBound Moment.probes k ≤ (campaignEnvelope N R T).logSize :=
  prefix_log_cap Moment.probes k (depth N) ((2*(N+1))^604) hk (probeBranchPow_le N)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
