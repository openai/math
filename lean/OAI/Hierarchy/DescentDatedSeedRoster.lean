import OAI.Hierarchy.DescentSeedOriginCapacity
import OAI.Hierarchy.DescentSeedRenamedRoster
import OAI.Hierarchy.DescentVenueRosterDefinition

namespace OAI
/-! # The original ranked neighbor roster in the named date-zero venue -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot
open DescentPackedSeed DescentSeedInitialTable DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage
open Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
  {k z wire s H cp p : ℕ} (X : Approximation F cp p)
  {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×DescentColonies.Block k}
  (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) c digits)
local notation "r" => o.raw
local notation "V₀" => Vertex X

private theorem transported_roster {P : Type} {n : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F n P bits}
    (R : Reached W G q ε S k 0 z 3 wire s) (size : Fintype.card R.V=Fintype.card V₀)
    (nearby : ∀v u,u∈R.placement.near v ↔
      OriginalRoster.ticket X R size u∈near X.network.copyGraph (OriginalRoster.ticket X R size v))
    (eqn : world R=W') (wide : Fintype.card (SeedNamed.transport R eqn).V≤H)
    (room : Fintype.card V₀≤H) :
    (SeedNamed.transport R eqn).venueRoster wide=
      roster X ((Fintype.equivFin V₀).toEmbedding.trans (Fin.castLEEmb room)) :=
  OriginalRoster.renamed_roster X R size nearby eqn wide room

theorem source_roster (wide : Fintype.card (r).V≤H) (room : Fintype.card V₀≤H) :
    o.source.venueRoster (source_hosts X o wide)=
      roster X ((Fintype.equivFin V₀).toEmbedding.trans (Fin.castLEEmb room)) := by
  unfold Origin.source
  have saved:=transported_roster (W := (initialGroup X S.copies s).state c)
    (W' := initial_world X S.copies s (S.groupCount 0) k digits c)
    (G := G) (S := S) (q := q) (ε := ε) (k := k) (z := z) (wire := wire) (s := s)
    X o.raw o.seed.hostSize o.seed.nearby
    (linked_world X c digits o.seed) (source_hosts X o wide) room
  exact saved

theorem source_host_size : Fintype.card o.source.V=Fintype.card V₀ := by
  unfold Origin.source
  have hosts:=SeedNamed.transport_card (W := (initialGroup X S.copies s).state c)
    (W' := initial_world X S.copies s (S.groupCount 0) k digits c)
    (G := G) (S := S) (q := q) (fee := ε) (k := k) (z := z) (wire := wire) (s := s)
    o.raw (linked_world X c digits o.seed)
  exact hosts.trans o.seed.hostSize

end
end Hierarchy.DescentDatedSeedStartup

end OAI
