import OAI.Hierarchy.DescentRegisterTypes
import OAI.Hierarchy.DescentDatedStageVenue
import OAI.Hierarchy.DescentVenueRosterDefinition

namespace OAI
/-! # Meaning of the physical register count and venue at a reached date -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
namespace DatePorts
def held (p : DatePorts) {F P : Type} [Field F] {d : ℕ} {bits:P→ℕ} {U : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist w : ℕ}
    (r : Reached U G q ε S k i z D wire hist) (floor : ℕ) (m : Memory w) : Prop :=
  ∃ wide : Fintype.card r.V≤p.venue.hosts,
    stageVenue r wide p.io p.venue.lanes p.venue.paidBits floor (r.venueRoster wide) m ∧
      m p.archive.count.base=(Fintype.card r.V:Word w)

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
