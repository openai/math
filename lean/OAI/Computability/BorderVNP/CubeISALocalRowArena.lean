import OAI.Computability.BorderVNP.CubeISALocalRowGeometrySpace
import OAI.Computability.BorderVNP.RoutingISACubeArena

/-! # Local declaration workspace within the full concrete evaluation arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open BorderVNP.Cube BorderVNP.Cube.Physical.Owned BorderVNP.Cube.Tally CubeHeaderInstall

/-- The power-table extent follows the entire local checker and lies within
the actual post-geometry cube allocation. -/
theorem arenaExtents (a : CubeArena.Layout) :
    a.header.packetBase ≤ a.packetEnd ∧ a.singleBank ≤ a.powerBase ∧
    a.powerBase+(a.n+1) ≤ a.stop := by
  refine ⟨by simp [CubeArena.Layout.packetEnd,bankStop],?_,?_⟩
  · dsimp [CubeArena.Layout.powerBase,CubeArena.Layout.ordinalBase,CubeArena.Layout.widthBase,
      CubeArena.Layout.dataMean,CubeArena.Layout.cableMean,CubeArena.Layout.demands,
      CubeArena.Layout.nodes,CubeArena.Layout.heads,CubeArena.Layout.publicBase,CubeArena.Layout.vertexBase]
    omega
  · dsimp [CubeArena.Layout.stop,CubeArena.Layout.cellBank,CubeArena.Layout.pairBase,
      TableLayout.reserveEnd,CubeArena.Layout.records,CubeArena.Layout.hostDirectory,
      CubeArena.Layout.pairDirectory,CubeArena.Layout.ownerBase,CubeArena.Layout.teamTotals,
      CubeArena.Layout.groupWeights]
    omega

/-- A single high-water word bound and the fixed-template fit place all local
roles. The same bound covers both the fixed selector loops and the variable
product-label endpoint and trial counters. -/
theorem space_of_arena (a : CubeArena.Layout) (w frame : ℕ)
    (axes : a.header.a = a.n+1) (alphabet : 0 < a.header.d) (blocks : 0 < a.header.blocks)
    (primary : frame+63 < a.header.header) (endRoom : a.stop < 2^w)
    (fixedFit : templateLimit a.n a.b a.h a.K a.s < 2^w)
    (positive : 0 < bankWidth a.n a.b a.h a.K a.s) :
    let stat := a.header
    let l := rowLayout stat a.b a.h a.powerBase
    Space l w a.n a.b a.h a.K a.s frame (stat.header+13) (stat.header+13+stat.entries) ∧
    stat.d^(a.n+1) < 2^w ∧ packetTrials a.n stat.d stat.blocks*(a.h*a.s) < 2^w := by
  obtain ⟨_,ab,high⟩ := arenaExtents a
  apply space_of_bankStop a.header w a.n a.b a.h a.K a.s a.powerBase frame axes alphabet blocks primary
    (by omega)
  · change a.singleBank < 2^w
    omega
  · exact fixedFit
  · exact positive

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
