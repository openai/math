import OAI.Computability.VPVNP.PairVertexLevelSchedule

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open Compression PairSimulation.VertexLevel

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
variable {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T h X).Choices)
local notation "passes" => executeLevels B f hf T h X z

/-- Every shrinking pass has a following pass on its selected branch. -/
theorem executeLevels_shrink_succ_lt (i : Fin (passes).length)
    (shrink : passes[i].origin.ordinal < S.steps) : i.val + 1 < (passes).length := by
  rw [selected_pass_ordinal B f hf T h X z i] at shrink
  by_contra! last
  have finalIndex : i.val + 1 = (passes).length := by have := i.isLt; omega
  have zero : (i.val + 1) % (S.steps + 1) = 0 := by
    rw [finalIndex, selected_pass_count B f hf T h X z, Nat.mul_mod_left]
  rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt (Nat.add_lt_add_right shrink 1)] at zero
  omega

end CompressorRecords

end VPVNP
end Computability
end OAI
