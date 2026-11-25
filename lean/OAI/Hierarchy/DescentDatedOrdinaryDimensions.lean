import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Dimensions of one ordinary compiler date -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated
open DescentSIMDLookup
noncomputable section
/-- Counts known when placing one ordinary date. The roster itself stays at its earlier address. -/
structure Ordinary where
  H : ℕ
  G : ℕ
  k : ℕ
  b : ℕ
  D : ℕ
  cap : ℕ
  payload : ℕ
  unit : ℕ
  profile : ℕ
  seats : ℕ

namespace Ordinary
variable (a : Ordinary)
def lanesAt := lanes a.payload a.unit
end Ordinary
end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

end OAI
