import OAI.Hierarchy.DescentSeedInitialWorldCodes
import OAI.Hierarchy.DescentSeedWorldNames
import OAI.Hierarchy.DescentSeedLinkFields

namespace OAI
/-! # One initial named history before all nonlinear choices and all realized placements -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentColonies DescentInitialHost DescentSeedRoot DescentPhysicalOrder
open Computability.BorderVNP.Crossing ThreeFlat Routing Catalyst
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins)

section Link
variable {G : PoweredGadget F} {S : AtomSchedule} {wire z s k : ℕ} {q ε : ℝ}
  (c : (initialGroup X S.copies s).Choice)
  {r : Reached ((initialGroup X S.copies s).state c) G q ε S k 0 z 3 wire s}
  (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k) (L : Chronology.SeedLink X c r digits)
include L
local notation "slot" => inputSlot X S.copies s (S.groupCount 0) k digits c

theorem linked_slot (u : ((initialGroup X S.copies s).state c).graph.Site) :
    (r.placement.siteSlot r.vertex r.valid.coordinates u).val=(slot u).val := by
  rw [GroupStage.siteSlot_val,inputSlot_val]
  have pos:=L.coordinates_read u
  simp only [pos.1,pos.2,L.hostSize,L.blocks,seedBlock]

theorem linked_site : site r=canonicalSite X S.copies s (S.groupCount 0) k digits c := by
  apply congrArg DescentPhysicalOrder.rename
  ext u
  change (r.placement.site r.vertex r.valid.coordinates u).val=(DescentPhysicalOrder.physical
    ((slot).toEmbedding.trans Fin.valEmbedding) u).val
  rw [GroupStage.site_val,DescentPhysicalOrder.physical_val]
  simp only [Function.Embedding.trans_apply,Fin.valEmbedding_apply,Equiv.toEmbedding_apply,linked_slot X c digits L]

theorem linked_edge : edge r=canonicalEdge X S.copies s c := by
  simp only [edge,canonicalEdge,L.edges]

theorem linked_world : world r=initial_world X S.copies s (S.groupCount 0) k digits c := by
  unfold world initial_world;rw [linked_site X c digits L,linked_edge X c digits L]

end Link
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
