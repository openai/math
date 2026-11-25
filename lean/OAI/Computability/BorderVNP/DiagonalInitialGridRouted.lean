import OAI.Computability.BorderVNP.DiagonalInitialGridWords
import OAI.Computability.BorderVNP.DiagonalInitialSiteWords
import OAI.Computability.BorderVNP.DiagonalPowerTransport
import OAI.Computability.BorderVNP.PackedGridPlacement

/-! # The tagged grid chosen by the ordered route placement

The hidden variables belong to the routed fine network, including its inserted
equality boxes. Public vertex identifiers and channels are the Cayley placement
of Proposition 7.2, with its certified congestion width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPlacement

open Crossing Diagonal.CellEntries Shortening
open scoped BigOperators Classical

variable {D b : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    {G J : Type} [Group G] [Fintype G] [Fintype J]
    {place : N.Site → G} {step : J → G} {invStep : ∀ j, ∃ k, step k = (step j)⁻¹} {k h : ℕ}
    (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (r : Routed N place step invStep k h) (unit : ∀ e, N.width e ≤ 1)

/-- A fine hidden assignment in each *actual routed* private box. -/
abbrev PrivateAssignments :=
  ∀ i, (N.subdivide (wireRoutes position r)).InsideAssignment (cell position r) i

/-- Channel numbering and the congestion certificate used by the placed grid. -/
noncomputable def routedPacking :
    ((N.subdivide (wireRoutes position r)).cellNetwork (cell position r) position).ChannelPacking
      (fun q : G × J => q.1) (fun q => q.1 * step q.2) (cableWidth G k h) :=
  (N.subdivide (wireRoutes position r)).cayleyPacking (cell position r) position step _
    (fun e => (WalkLayout.adjacent N (CayleyPaths.graph step invStep) place r.walk position e).2)
    (outgoing_le position r unit)

variable {Team Param Gadget E : Type*} [Fintype Team] [Fintype Param]
    {tags : N.Tables (Entry Param Gadget)} (sites : PowerSites Team Param Gadget b N tags)

/-- Each fixed private assignment gives one tagged grid table. -/
noncomputable def privateGridTags (tags : N.Tables (Entry Param Gadget)) (z : PrivateAssignments position r) :
    (N.cayleyGrid place position step (cableWidth G k h)).Tables (Entry Param Gadget) :=
  conditionedGridTags (cell position r) position (routedPacking position r unit)
    (N.subdivideTables (wireRoutes position r) tags) z

/-- The placement supplies the true coarse owners and fine selected bits. -/
noncomputable def privateGridWords (z : PrivateAssignments position r) :
    PowerWords Team Param Gadget b (N.cayleyGrid place position step (cableWidth G k h))
      (privateGridTags position r unit tags z) :=
  ((sites.subdivision (wireRoutes position r)).toWords).gridWords (cell position r) position z
    (routedPacking position r unit)

/-- The public owner of each original occurrence is precisely its selected placement cell. -/
theorem privateGridWords_site (z : PrivateAssignments position r) (w : PowerSlot Team Param b) :
    (privateGridWords position r unit sites z).site w = place (sites.site w) := rfl

variable [CommSemiring E] (values : Gadget → E)

omit [Fintype Param] in
private theorem interpret_subdivide (routes : N.WireRoutes) (v : (N.subdivide routes).Site) (a x) :
    interpret values (N.subdivideTables routes tags v a x) =
      N.subdivideTables routes (fun i z y => interpret values (tags i z y)) v a x := by
  rcases v with old | new
  · rfl
  · simp only [Network.subdivideTables]
    split <;> simp

omit [Fintype Param] in
/-- Summing the conditioned private tables on the real public grid recovers
the fine contraction, including every equality introduced along the private routes. -/
theorem sum_privateGrid_value (x : Ports bits) :
    (∑ z : PrivateAssignments position r, (N.cayleyGrid place position step (cableWidth G k h)).value
      (fun v a y => interpret values (privateGridTags position r unit tags z v a y)) x) =
      N.value (fun v a y => interpret values (tags v a y)) x := by
  have hs := sum_conditioned_grid_value (cell position r) position (routedPacking position r unit)
    (N.subdivideTables (wireRoutes position r) tags) values x
  simp_rw [interpret_subdivide] at hs
  exact hs.trans (N.value_subdivide (wireRoutes position r) _ x)

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI
