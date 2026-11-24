import OAI.Computability.VPVNP.PairVertexDispatch

/-! # The three readers reached through the stored native vertex tag -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open DFS

/-- Use the parser at the selected native entry, in the same role order as
the decoder of the published tag word. -/
def handlers {w n : ℕ} (leaf shrink refresh : HookParser w n) :
    NodeDispatch.Role → HookParser w n
  | .leaf => leaf
  | .shrink => shrink
  | .refresh => refresh

end PairSimulation.VertexImage.RoleDomains

end VPVNP
end Computability
end OAI
