import OAI.Computability.BorderVNP.CubePhysicalGreedyTally
import OAI.Computability.BorderVNP.RoutingISASignedTaskArena

/-! # Native greedy owners on the registered planner coordinates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open BorderVNP.Cube Cube.Physical

/-- The actual greedy owner remains the owner of the declared packet when
the emitter layout and its receiving cells are reindexed together. -/
theorem Layout.greedyOwner_reindex {T : Type*} [Fintype T] {R : ℕ} {physical planner : Layout}
    (same : physical=planner)
    (label : Fin physical.cube.cells → Cube.Label (physical.cube.n+1) physical.cube.header.d)
    (recv : T → Fin physical.cube.cells) (widths : T → ℕ)
    {owner : (Cube.Packet planner.cube.n planner.cube.header.d planner.cube.header.blocks →
        Cube.Selector planner.cube.n planner.cube.K planner.cube.h) → Fin planner.cube.header.d → Fin (R+1)}
    (auth : HEq owner (greedyOwner (blocks:=physical.cube.header.blocks) (K:=physical.cube.K) (h:=physical.cube.h)
      R physical.cube.b physical.cube.s label recv widths)) :
    owner=greedyOwner (blocks:=planner.cube.header.blocks) (K:=planner.cube.K) (h:=planner.cube.h)
      R planner.cube.b planner.cube.s
      (cast (congrArg (fun t : Layout => Fin t.cube.cells → Cube.Label (t.cube.n+1) t.cube.header.d) same) label)
      (cast (congrArg (fun t : Layout => T → Fin t.cube.cells) same) recv) widths := by
  subst planner
  exact eq_of_heq auth

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
