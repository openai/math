import OAI.Hierarchy.PaperBoundsFromPurchasedHosts
import OAI.Hierarchy.DescentPurchasedOriginalHosts

namespace OAI
/-! # Arithmetic class separations and square matrix multiplication over every field -/
namespace Hierarchy
open LinearAlgebra.SpectralBooks ThreeFlat DescentSixParty
noncomputable section

private theorem purchased_hosts (p : ℕ) [Fact p.Prime] (G : PoweredGadget (ZMod p)) (c : EpochRotor G) :
    ∃ drift limit : ℕ, c.ProducesHosts drift limit :=
  ⟨c.hostDrift,c.hostDegree,c.produces_original_hosts⟩

/-- Prime fields admit spectral flats of unbounded dimension. -/
theorem prime_flats : UnboundedPrimeFieldFlats :=
  unbounded_prime_flats_from_purchased_hosts purchased_hosts

end
end Hierarchy
end OAI
