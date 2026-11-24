import OAI.Computability.VPVNP.RAMTapeSiteGraphInput

/-!
# Complete physical simulation of a site's capped native burst calls

The fixed graph begins with the initialization slot, starts every call from
fresh registers and private memory, and observes the real external actions
of the template. Its unique terminal behavior follows the native validator
on every possible private choice string.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteCutBank

open BurstRAM PrivateRAM SiteProcessor

variable {d e w p r k : ℕ}

theorem Input.graphOutcome (x : Input d e w) (T : Template p r k) (pub : Fin k → Word w)
    (bits : List Bool) (_hvalid : x.valid) :
    ∃ t ≤ graphBudget r w e (x.n^x.u), x.GraphOutcome T pub bits t :=
  x.asWordSite.graphOutcome T pub bits

end RAMTape.SiteCutBank

end VPVNP
end Computability
end OAI
