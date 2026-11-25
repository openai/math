import OAI.Hierarchy.TaggedWideCarriedRoom
import OAI.Hierarchy.ProbeFixedWideSpillControlFields
import OAI.Hierarchy.ProbeFixedWideSpillFieldRoom

namespace OAI
/-! # Native word room for the two overlap accumulators at a spill turn -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
theorem wide_neighbor_double_word (h width unitCost : ℕ)
    (large : HistoryRoles.stride k v.sampler.degree v.wideJobs * v.wideHistoryUnit unitCost≤h)
    (small : width≤2^h) : 2*v.wideNeighborCap width unitCost<2^(Native.wordBits h (2^v.W) Native.copies) := by
  let d:=HistoryRoles.stride k v.sampler.degree v.wideJobs*v.wideHistoryUnit unitCost
  have block : d*width<2^(h+h):=by
    rw [pow_add]
    exact (Nat.mul_le_mul_left _ small).trans_lt
      (Nat.mul_lt_mul_of_pos_right (large.trans_lt (Nat.lt_two_pow_self (n:=h))) (Nat.two_pow_pos _))
  have digits : v.wideNeighborDigits width unitCost≤h+h:=
    (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr block
  have count : h+h+1<Native.wordBits h (2^v.W) Native.copies:=by
    unfold Native.wordBits ProbeStage.roomBits
    omega
  change 2*2^(v.wideNeighborDigits width unitCost)<_
  rw [Nat.mul_comm,←pow_succ]
  exact Nat.pow_lt_pow_right (by decide : 1<2) ((Nat.add_le_add_right digits 1).trans_lt count)
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
