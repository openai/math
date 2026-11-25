import OAI.Hierarchy.DescentSeedRosterCoordinate
import OAI.Hierarchy.DescentSeedWorldNames

namespace OAI
/-! # Renaming the seed's sites and cables preserves its ranked host roster -/
namespace Hierarchy.DescentDatedSeedStartup.OriginalRoster
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentSeedInitialTable Catalyst
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist H cp p : ℕ}
    (X : Approximation F cp p) (R : Reached W G q ε S k i z 3 wire hist)
    (size : Fintype.card R.V=Fintype.card (Vertex X))

include size in
/-- The site and cable permutations preserve the roster on the same physical host names. -/
theorem renamed_roster
    (nearby : ∀v u,u∈R.placement.near v ↔ ticket X R size u∈near X.network.copyGraph (ticket X R size v))
    (identified : world R=W') (width : Fintype.card (identified ▸ reached R : Reached W' G q ε S k i z 3 wire hist).V≤H)
    (publicWidth : Fintype.card (Vertex X)≤H) :
    (identified ▸ reached R : Reached W' G q ε S k i z 3 wire hist).venueRoster width=
      roster X ((Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWidth)) :=by
  cases identified
  exact raw_roster X R size nearby width publicWidth

include size in
theorem renamed_host_count (identified : world R=W') :
    Fintype.card (identified ▸ reached R : Reached W' G q ε S k i z 3 wire hist).V=Fintype.card (Vertex X) :=by
  cases identified
  exact size

end
end Hierarchy.DescentDatedSeedStartup.OriginalRoster

end OAI
