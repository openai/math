import OAI.Computability.VPVNP.LiveCompressedPairSourceCaps
import OAI.Computability.VPVNP.LiveCompressedPairHandoff
import OAI.Computability.VPVNP.LiveProgramCompressedPairPaths

/-! # The reduced terminal cutoff covers the selected physical ordinal -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM LiveStageLink PairStages.Group.CompressedPaths

set_option exponentiation.threshold 10000 in
/-- The inner terminal dispatcher and the enclosing live-pair dispatcher
both consume ticks before entering the vertex phase. -/
theorem terminal_ordinal_room (G : PairStages.Group) {n : ℕ} (hn : 128 ≤ n)
    (clock : G.clock = n ^ 10000) : n ^ 9999 ≤ clockAt (publicWords G) (fuel G) Stage.terminal := by
  have outer : n ^ 9999 + 107 ≤ fuel G := private_clock_room G hn clock
  have dispatch : (LiveStageLink.dispatchEvents (PairTag.address (publicWords G))
    Stage.terminal).length ≤ 22 := by
    simp only [LiveStageLink.dispatchEvents,List.length_cons,List.length_replicate]
    decide
  unfold clockAt
  omega

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
