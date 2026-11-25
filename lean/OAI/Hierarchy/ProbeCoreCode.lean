import OAI.Hierarchy.ProbeCoreBoard

namespace OAI
/-! # The finite integer length code of each genuine core edge -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe
open scoped Classical
variable (S : PurchaseSampler)

def coreCode {h d k : ℕ} (M : ℕ) : Edges S h d k → ℕ
  | .inl (.inl _) => M
  | .inl (.inr (.inl _)) => ⌈Real.sqrt 2*(M:ℝ)⌉₊
  | .inl (.inr (.inr _)) => 0
  | .inr _ => 1

theorem coreCode_read {h d k : ℕ} (M : ℕ) (e : Edges S h d k) :
    (coreCode S M e:ℝ)=coreLength (freeLength M) e := by
  rcases e with e|e
  · rcases e with e|e
    · rfl
    · rcases e with e|e
      · exact natCast_ceil_eq_intCast_ceil (by positivity : 0 ≤ Real.sqrt 2 * (M : ℝ))
      · rcases e with e | e <;> simp [coreCode,coreLength,freeLength]
  · simp [coreCode,coreLength]

end Hierarchy.ProbeStage.CoreBoard
end

end OAI
