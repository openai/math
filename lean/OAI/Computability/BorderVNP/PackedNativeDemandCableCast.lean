import OAI.Computability.BorderVNP.PackedNativeDemandRows

/-! # Reindexing the private and live placement tables of native demands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing

variable {D C ne ne' np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (he : ne = ne') (port : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (gap : ℕ)

/-- The entire native table of original descriptor placements, including its default
outside the declared entries, is invariant under reindexing the cable rectangle. -/
theorem privatePair_cast_cables :
    privatePair N cell (edge.trans (finCongr he).toEmbedding) port dir old live gap =
      privatePair N cell edge port dir old live gap := by
  subst ne'
  rfl

/-- The team-major live placement table has the same addresses at every index. -/
theorem livePair_cast_cables :
    livePair N cell (edge.trans (finCongr he).toEmbedding) port dir old live gap =
      livePair N cell edge port dir old live gap := by
  subst ne'
  rfl

/-- The original ordered list of seven-word demand rows, including the widths
that index later claims, survives the cable rectangle cast. -/
theorem rows_cast_cables :
    rows N cell (edge.trans (finCongr he).toEmbedding) port dir old live gap =
      rows N cell edge port dir old live gap := by
  subst ne'
  rfl

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
