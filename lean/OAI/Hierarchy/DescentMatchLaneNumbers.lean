import OAI.Hierarchy.DescentPackedMatchShape

namespace OAI
/-! # Public bit widths of the match, topology, profile and birth fields -/

namespace Hierarchy.DescentPacking.PackedMatch.ProfileTable
def envelope (s : Shape) := s.bits+3*(s.digit*s.pairs)
end Hierarchy.DescentPacking.PackedMatch.ProfileTable

namespace Hierarchy.DescentPacking.PackedMatch.SixBirths
def unit (s : Shape) := max (s.digit*s.pairs+s.outputBits) ((s.digit+1)*(s.pairs*6))
end Hierarchy.DescentPacking.PackedMatch.SixBirths

namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather
def matchUnit (s : Shape) (panelWidth r D p : ℕ) :=
  max (panelWidth*fields r D p+panelWidth) (ProfileTable.envelope s)
end Hierarchy.DescentPacking.PackedMatch.Local.Gather

end OAI
