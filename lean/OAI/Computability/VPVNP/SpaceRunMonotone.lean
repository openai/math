import OAI.Computability.VPVNP.UniversalCountStackBounds

/-! # Enlarging a bound on the height of each machine stack -/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalCountStack

/-- Enlarge a uniform height bound on every configuration of the same machine run. -/
theorem SpaceRun.mono_cap {K Q : Type*} [DecidableEq K] {code : RAMTape.StackCode K Q}
    {a b t q s q' s'} (h : SpaceRun code a t q s q' s') (hab : a ≤ b) :
    SpaceRun code b t q s q' s' := by
  induction h with
  | nil q s hs => exact .nil q s fun k ↦ (hs k).trans hab
  | cons hs step _ ih => exact .cons (fun k ↦ (hs k).trans hab) step ih

end UniversalCountStack

end VPVNP
end Computability
end OAI
