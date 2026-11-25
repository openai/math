import OAI.Hierarchy.DescentWalshLaneMedian
import OAI.Hierarchy.DescentResetDigits

namespace OAI
/-! # The real first-reset lane choice either fits every group or pays the short fields -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentPackedWalsh DescentWalshDyadicBudget
theorem reset_fill (S : AtomSchedule) (k tail age payload word factor bits : ℕ)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k) (nonzero : 0<bits)
    (room : k≤laneBits (S.groupWidth k tail age+k) payload bits) (cpu : word≤factor*payload) :
    let n:=laneBits (S.groupWidth k tail age+k) payload bits
    S.groupCount age≤2^(n-k) ∨ word≤2^(n-k)*(16*factor*bits*2^k) :=by
  intro n
  have split : 2^n=2^(n-k)*2^k :=by rw [←pow_add,Nat.sub_add_cancel room]
  rcases laneBits_median (S.groupWidth k tail age+k) payload bits nonzero with all|packed
  · left
    have eqn : 2^(n-k)*2^k=(S.groupCount age)*2^k :=by
      rw [←split,show 2^n=2^(S.groupWidth k tail age+k) from all,pow_add,S.group_power groups radix age]
    exact (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) eqn).ge
  · right
    calc
      word≤factor*payload :=cpu
      _≤factor*(16*bits*2^n) :=Nat.mul_le_mul_left _ packed
      _=_:=by rw [split];ring

end Hierarchy.DescentDatedSeedStartup

end OAI
