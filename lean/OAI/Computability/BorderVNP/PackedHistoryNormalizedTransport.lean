import OAI.Computability.BorderVNP.PackedHistoryNormalizedBoundary

/-! # Exact boundary rows at equal congruence depths and rectangles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Adaptive PublicCapacity

variable {q w a b : ℕ} {inner outer : Shape}

/-- Read the same route column after rewriting its depth and rectangle. -/
def returnedPin {Move : Type*} (hlev : a = b) (hshape : outer = inner) :
    RouteRows.Pins Move q (b+1) outer.sites outer.edges w →
    RouteRows.Pins Move q (a+1) inner.sites inner.edges w := by
  subst b; subst outer; exact id

variable {D : ℕ} {P I : Type} [Fintype I] {K : Type*} {bits : P → ℕ} {p : Pack D P bits K} {L : ℝ}

/-- Keep every real row number when the scheduled rectangle is rewritten. -/
def returnedRows (hshape : outer = inner) (rows : Rows inner p.layout) : Rows outer p.layout := hshape ▸ rows

/-- Keep the physical dummy endpoint attached to each vacant scheduled row. -/
def returnedDummy (hshape : outer = inner) (dummy : Fin inner.edges → p.layout.Site) :
    Fin outer.edges → p.layout.Site := hshape ▸ dummy

/-- The transported wires encode exactly the transported integral routes and
row directory, including dummy endpoints and the winning motion. -/
theorem returnedReady (enum : Fin q ≃ I) {route : SiteRoutes p I a L}
    {rows : Rows inner p.layout} {dummy : Fin inner.edges → p.layout.Site}
    {z : RouteRows.Pins (allowedMoves I L) q (a+1) inner.sites inner.edges w → Bool}
    (hlev : a = b) (hshape : outer = inner) (ready : RouteRows.Ready enum p route rows dummy z) :
    RouteRows.Ready enum p (reindexRoutes hlev route) (returnedRows hshape rows)
      (returnedDummy hshape dummy) (z ∘ returnedPin hlev hshape) := by
  subst b; subst outer; exact ready

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
