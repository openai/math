import OAI.Hierarchy.DescentVenueShape

namespace OAI
/-! # The native gather and pitch-transfer charge of a fixed array of input expressions -/
namespace Hierarchy.DescentVenueSlabs.ExprInputs
open DescentSIMDLookup
noncomputable section

def tariff (s : Shape) (T : ℕ) :=
  let oldRows := s.hosts * chunks s.groups s.sourceLanes
  let hosts := s.pages * s.hosts
  (4 + s.pages * (4 + oldRows * (2*T + 4))) + 7*(15 + s.pages * (11 + 4*T)) +
    2048*((Overlap.pieces s.groups s.sourceLanes s.targetLanes + 1) *
      (s.sourceLanes + 1) * 2^(s.bits * s.sourceLanes) +
      Overlap.rows hosts s.groups s.sourceLanes + Overlap.rows hosts s.groups s.targetLanes + 1)

end
end Hierarchy.DescentVenueSlabs.ExprInputs

end OAI
