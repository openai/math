import OAI.Hierarchy.DescentRotorAlphabet

namespace OAI
namespace Hierarchy.DescentOrdinaryPalette
/-- Public primitive palette of the run and the held and working batch sizes at this date. -/
structure Configuration where
  rotor : DescentSixParty.RotorSpec
  seedWidth : ℕ
  grainLimit : ℕ
  priorLanes : ℕ
  workLanes : ℕ
  nextLanes : ℕ
end Hierarchy.DescentOrdinaryPalette

end OAI
