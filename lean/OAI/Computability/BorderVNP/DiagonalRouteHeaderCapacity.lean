import OAI.Computability.BorderVNP.CubeRouteHeaderCapacity
import OAI.Computability.BorderVNP.DiagonalEpochScales

/-! # Joint header and link capacities on the chosen epoch schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing PackedHistoryCircuit.Normalized Filter

variable {D m a extra : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m} {S : SiteSchedule e}

/-- The chosen epoch exponents simultaneously bound the emitted headers and
guarantee that the actual data and shared incidences fit all native links. -/
theorem EpochScales.eventually_routed_headers (s : EpochScales S (a+1) extra) :
    ∀ᶠ n : ℕ in atTop, Cube.RouteRecords.HeaderFitsAt s.α a n ∧ Cube.RouteRecords.FitsLinksAt s.α ((s.τ:ℝ)/5) n := by
  have ha : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have ht : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  exact (Cube.RouteRecords.eventually_emitted_headers a ha (by linarith [s.alpha_small])).and
    (Cube.RouteRecords.eventually_leg_capacity_of_incidence (by positivity) (by linarith [s.tau_small]) (by linarith [s.tau_small,s.alpha_small]))

end Diagonal

end BorderVNP
end Computability
end OAI
