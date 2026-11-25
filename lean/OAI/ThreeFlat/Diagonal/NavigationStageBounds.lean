import OAI.ThreeFlat.Diagonal.NavigationDirectory

namespace OAI
/-! # Local child-kernel and half-edge count bounds of a physical stage -/
namespace ThreeFlat.Diagonal.NavigationPass
open NavigationDirectory

def stageHalves : Stage → ℕ
  | .shrink x => 2*x.newDegree
  | .refresh _ _ _ h pad => 2*(1+h+pad)

def stageMotifs : Stage → ℕ
  | .shrink x => x.localCapacity
  | .refresh .. => 1

end ThreeFlat.Diagonal.NavigationPass

end OAI
