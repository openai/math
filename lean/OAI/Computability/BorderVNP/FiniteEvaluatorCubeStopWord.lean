import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenRoom

/-! # The cube's last address in a fitted evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

/-- A word which holds the signed evaluator's end address also holds every
address up to the end of its cube. The constant deck precedes the task arena. -/
theorem Layout.cube_stop_lt_word (t : Layout) {w u v k : ℕ}
    (fit : t.endAddress w u v k < 2^w) : t.cube.stop < 2^w := by
  apply lt_of_le_of_lt _ ((t.before_limit_le_endAddress w u v k).trans_lt fit)
  apply le_trans _ (show t.before.start ≤ t.before.limit by rw [t.before.footprint]; omega)
  apply le_trans _ t.constants_le_before
  unfold CubeConstants.arenaEnd CubeConstants.idBase
  omega

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
