import OAI.Computability.NearSquareRoot.ScheduleRegisterConstructors
import OAI.Computability.IntegerMultiplication.Code.Fold

/-! # Register-preserving map and fold -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterWitness
open IntegerMultiplication Code CommonRegisters

@[simp] theorem rightBody_within {R : ℕ} {base cmd : Cmd} (hR : 3 ≤ R) :
    Within R (Task.rightBody base cmd) ↔ Within R base ∧ Within R cmd := by
  simp [Task.rightBody,Within,move,forward,forwardBody,flood,give,pack]
  grind

/-- A fixed register cutoff also suffices for arbitrary list lengths. -/
theorem Easy.mapping {X Y : Type*} [Codec X] [Codec Y] {f : X → Y}
    {R : ℕ} (hR : 4 ≤ R) (h : Easy R f) : Easy R (List.map f) := by
  have : 3 ≤ R := by omega
  exact register_witness R from Code.Easy.mapping (forget h)

end RegisterWitness

end NearSquareRoot
end Computability
end OAI
