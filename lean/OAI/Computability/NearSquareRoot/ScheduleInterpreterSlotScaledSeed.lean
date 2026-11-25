import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotInstallCells

/-! # The intermediate fence measured on the index tape -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotScaledBroadcast
variable {A I : Type} [DecidableEq I]

/-- Only the auxiliary head has measured the right endpoint. The two
temporary origin bits remain set on every tape. -/
def seed (f : I → ℤ → A) (L : ℕ) (aux : I) (j : I) : ℤ → Fence.Symbol A :=
  SlotInstall.paint f L true (decide (j=aux)) (fun _ => false) j

end Uniform.SlotScaledBroadcast

end NearSquareRoot
end Computability
end OAI
