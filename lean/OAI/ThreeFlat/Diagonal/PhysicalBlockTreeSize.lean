import OAI.ThreeFlat.Diagonal.PhysicalBlockCharge
import OAI.ThreeFlat.Diagonal.PhysicalTreeSize

namespace OAI
/-! # Uniform ancestor counts for repetitions of a fixed physical block -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage

open HistoryContraction
variable {F : Type} [Field F]

namespace Block
variable (B : Block F)

/-- The actual composed placement, with all histogram choices specified by
the history, has at most this many oldest positions in each final cell. -/
theorem oldest_positions_le (n rem : ℕ)
    (A : State (2^(B.exponent 0)) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History)
    (v : (((B.repeat n).run rem A).plan.finish h).Site) :
    Nat.card {x // ((B.repeat n).run rem A).plan.destination h x = v} ≤ 2^(B.blockCharge*n) := by
  have exactSize := (B.repeat n).run_destinationSize rem A h v
  rw [exactSize,← B.charge_repeat]
  exact (B.repeat n).childrenProduct_le

theorem oldest_positions_u8 (u rem : ℕ)
    (A : State (2^(B.exponent 0)) ((B.repeat (u^8)).charge+rem))
    (h : ((B.repeat (u^8)).run rem A).plan.History)
    (v : (((B.repeat (u^8)).run rem A).plan.finish h).Site) :
    Nat.card {x // ((B.repeat (u^8)).run rem A).plan.destination h x = v} ≤
      (2^B.blockCharge)^((B.levels+1)*u^8) := by
  apply (B.oldest_positions_le (u^8) rem A h v).trans
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.mul_le_mul_left
  exact Nat.le_mul_of_pos_left _ (by omega)

end Block
end ThreeFlat.Diagonal.PhysicalStage

end
end OAI
