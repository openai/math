import OAI.Hierarchy.DescentSeedCableMeaning
import OAI.Hierarchy.DescentSeedRootRows
import OAI.Hierarchy.DescentReached

namespace OAI
/-! # The original paid seed receipt, including every physical signed word -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentInitialHost DescentColonies Catalyst
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k : ℕ}

/-- Certify a single immutable first world. Its scalar-node ordinal comes
from the public copy-by-vertex census. -/
structure SeedLink {cp pins : ℕ} (X : Approximation F cp pins) {wire s z : ℕ}
    (c : (initialGroup X S.copies s).Choice)
    (r : Reached ((initialGroup X S.copies s).state c) G q ε S k 0 z 3 wire s)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k) : Prop where
  edges : r.order=DescentSeedRoot.oldOrder X c
  vertices : HEq r.vertex (Fintype.equivFin (Site X.network.copyGraph)).toEmbedding
  position : HEq r.placement.pos (seedPos X c digits)
  blocks : r.placement.block=seedBlock X c digits
  records : HEq r.placement.records (seedRecords X c)
  counts : ∀v,(r.placement.records v).length=(seedRecords X c v).length
  hubs : (fun v=>r.placement.hub (r.placement.pos v).2)=seedHub X c
  hostSize : Fintype.card r.V=Fintype.card (Site X.network.copyGraph)
  hostHubs : ∀v : r.V,∃u : Site X.network.copyGraph,(r.vertex v).val=(Fintype.equivFin _ u).val ∧ r.placement.hub v=hubFlag X.network.copyGraph u
  capacity : r.placement.cap=256
  pinCoordinates : ∀pin,
    ((r.placement.pos (((initialGroup X S.copies s).state c).graph.attach pin)).1,
      r.placement.block (((initialGroup X S.copies s).state c).graph.attach pin))=digits pin.1
  pinHosts : ∀ (pin pin' : Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))),pin.2=pin'.2 →
    (r.placement.pos (((initialGroup X S.copies s).state c).graph.attach pin)).2=
      (r.placement.pos (((initialGroup X S.copies s).state c).graph.attach pin')).2
  pinRanks : ∀pin,(r.vertex (r.placement.pos (((initialGroup X S.copies s).state c).graph.attach pin)).2).val=
    (Fintype.equivFin (Site X.network.copyGraph) (.inr pin.2)).val
  coordinates_read : ∀u, (r.placement.pos u).1=(digits u.1).1 ∧
    (r.vertex (r.placement.pos u).2).val=(Fintype.equivFin (Site X.network.copyGraph) u.2).val

  /-- The physical graph retains the distinct original neighbors, including empty host rows. -/
  nearby : ∀v u, u∈r.placement.near v ↔
    DescentPackedSeed.Signed.Plane.initialTicket X r.vertex hostSize u∈
      near X.network.copyGraph (DescentPackedSeed.Signed.Plane.initialTicket X r.vertex hostSize v)

  signed : DescentPackedSeed.Signed.Plane.Receipt X S r.placement (r.order.trans Fin.valEmbedding) r.vertex hostSize
  cables : DescentPackedSeed.Signed.Plane.CableFields X S r.placement (r.order.trans Fin.valEmbedding) r.vertex

end
end Hierarchy.DescentSixParty.Chronology

end OAI
