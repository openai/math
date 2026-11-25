import OAI.ThreeFlat.Diagonal.TickWorkspace

namespace OAI
/-! # The receiver workspace below the original high journal -/

namespace Hierarchy.HistorySelectedHighStage
open ThreeFlat.Diagonal.TickWorkspace

/-- S60 and the whole read-only journal are addressable at the receiver's word width.
The original journal starts at sixteen times its grid sector. -/
theorem scale {w u : ℕ} (positive : 0<w) (workspace : u^10≤5*w) :
    base u 60+stride u<16*2^(32*w) ∧ 16*2^(32*w)<2^(64*w) := by
  have first : 64*stride u≤2^(32*w) := by
    change 2^6*(2^(u^10))^4≤2^(32*w)
    rw [←pow_mul,←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have nonempty : 0< stride u := by unfold stride;positivity
  refine ⟨?_,?_⟩
  · change 61*stride u+stride u<16*2^(32*w)
    omega
  · change 2^4*2^(32*w)<2^(64*w)
    rw [←pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by omega)

end Hierarchy.HistorySelectedHighStage

end OAI
