import OAI.Computability.VPVNP.PairShrinkRoleChild

/-! # The two pointers and ordered site list of a packed shrink child descriptor -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.PackedChildren

open BurstRAM Compression

/-- The child list begins immediately after the two-word popped-node header.
The caller's old level publishes the child-directory bank at offset fourteen. -/
def descriptor {a g w : ℕ} {Z : State a g} (head : Word w) (sites : List Z.network.Site)
    (node : Word w) : ChildArguments.Descriptor w Z := ⟨node.val + 2, head + 14, sites⟩

end PairSimulation.ShrinkRole.PackedChildren

end VPVNP
end Computability
end OAI
