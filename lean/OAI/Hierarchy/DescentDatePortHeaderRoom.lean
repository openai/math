import OAI.Hierarchy.DescentRegisterTypes

namespace OAI
/-! # Finite extents of the preceding chronology's actual host header -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
structure HeaderRoom (p : DatePorts) (w roof : ℕ) : Prop where
  count : p.archive.count.Fits w roof
  roster : p.io.roster.Fits w roof
  peers : p.venue.hosts*p.venue.degree≤p.io.roster.size
  hubs : p.io.hubs.Fits w roof
  hosts : p.venue.hosts≤p.io.hubs.size

theorem HeaderRoom.mono {p : DatePorts} {w floor roof : ℕ} (h : p.HeaderRoom w floor) (later : floor≤roof) :
    p.HeaderRoom w roof :=
  ⟨⟨h.count.1,h.count.2.1,h.count.2.2.trans later⟩,
   ⟨h.roster.1,h.roster.2.1,h.roster.2.2.trans later⟩,h.peers,
   ⟨h.hubs.1,h.hubs.2.1,h.hubs.2.2.trans later⟩,h.hosts⟩

end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
