import OAI.Hierarchy.DescentReached
import OAI.Hierarchy.DescentHostRosterOrder

namespace OAI
/-! # The padded rank-ordered neighbor table of any reached venue -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {age z D wire hist H : ℕ}
  (r : Reached W G q ε S k age z D wire hist)

/-- The geometric roster on the actual dense vertex order, extended by vacant padded hosts. -/
def Reached.venueRoster (wide:Fintype.card r.V≤H)(h:Fin H)(s:Fin D):Option (Fin H):=
  hostRotor (r.vertex.trans (Fin.castLEEmb wide)) (hostRoster r.placement (r.vertex.trans Fin.valEmbedding))
    h (Fin.cast r.branch.symm s)

end
end Hierarchy.DescentSixParty

end OAI
