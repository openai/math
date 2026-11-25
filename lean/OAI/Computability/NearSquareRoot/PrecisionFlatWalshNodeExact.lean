import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodePlan
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeChild
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshUnlane

/-! # Exact semantics of an internal node of the recursive Walsh tape program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshNode

open KernelPass PhysicalWalshNode

/-- Splitting the ordinal data into physical lanes, executing the ideal leaf
operations of the certified plan, and joining the lanes realizes one unitary
Walsh on precisely the active field, with its spectators in place. -/
theorem completeIdeal {a W : ℕ} (hW : 0 < W) (p : Plan (a+1) W W) (hp : Correct p)
    (s : Shape) (hl : 0 < s.level) (hd : W^s.level ∣ s.pref) (x : IdealRow) :
    atWidth (count (a+1) s) (idealUnlane (a+1) hW s
      ((idealOps a W (fun axis t => idealRow (a+1) (descend (a+1) W axis t))).applyPlan p s
        (idealLane (a+1) W s x))) = atWidth (count (a+1) s) (idealRow (a+1) s x) := by
  apply reassemble _ _ hW s hl hd
  intro g b t z
  apply correct_on_rowPos s g.val t _ _ p hp
  intro axis v u
  rw [idealRow_descend]
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg (fun c : ℂ => c * v (rowPos a s g.val z t))
    (by simpa only [Rat.cast_prod] using (FlatWalshKernel.packed_child_entry axis u z).symm)

end FlatWalshNode

end NearSquareRoot
end Computability
end OAI
