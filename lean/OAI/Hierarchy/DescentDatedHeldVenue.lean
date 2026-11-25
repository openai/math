import OAI.Hierarchy.DescentDatedRegisterState

namespace OAI
/-! # Reading a held venue at its published host and lane counts -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {U : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist w : ℕ}

theorem held_venue_at (ports : DatePorts) (r : Reached U G q ε S k i z D wire hist)
    {floor H lanes : ℕ} {m : Memory w} (wide : Fintype.card r.V≤H)
    (hostCount : ports.venue.hosts=H) (pitch : ports.venue.lanes=lanes)
    (kept : ports.held r floor m) :
    stageVenue r wide ports.io lanes ports.venue.paidBits floor (r.venueRoster wide) m := by
  subst H
  subst lanes
  obtain ⟨_,rows,_⟩:=kept
  exact rows

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
