import OAI.Computability.IntegerMultiplication.Param.Wage
import OAI.Computability.IntegerMultiplication.Grid.Stage

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Param
open Hook Haze Earth Net Filter
/- Grid Stage sheer eventually dominated. One specialization. -/
theorem paid (w: ℕ →ℕ) (c:ℕ)
    (q : Large fun n=> w n≤c*(budget n+1)) :
    ∃ k:ℕ,Large fun n=> Grid.mercy scouts batches chunk border w chunk faces n ≤ k*fund n := by
  obtain ⟨k,h⟩ := taxFund c
  refine ⟨k+24,?_⟩
  filter_upwards [batch,q] with n t v
  unfold Grid.mercy cost_ feeK forecast Haze.expense stairs Hook.altitude Ht Haze.expense
  rw [t.2]
  dsimp only
  push_cast
  have Z := h n _ v
  have P := permutationFare ((face_margin n).1.trans (face_margin n).2) (le_refl (chunk n))
  have Q := heightFare n
  push_cast at *
  linarith

theorem spar :
    Large fun n=> Phase.safe (scouts n) (chunk n) ∧ Phase.safe (scouts n) (border n) ∧
      Phase.safe (faces n) (chunk n) := by
  filter_upwards [safe] with n v
  have a : lanes n≤budget n := Nat.le_self_pow (by decide) _
  exact ⟨v _ _ ((Nat.sub_le ..).trans a) le_rfl (by omega),
    v _ _ ((Nat.sub_le ..).trans a) (border_v n).1 (border_v n).2,
    v _ _ ((face_margin n).1.trans (face_margin n).2) le_rfl (by omega)⟩

end Param

end IntegerMultiplication
end Computability
end OAI
