import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSwap

/-! # The named rectangle command on compact Walsh packets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileRect
open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode.SlotSwap

/-- All packets share one program. In the empty-wing case the trailing
payload can have any positive size. -/
def RectRuns (c : Cmd) (ρ : ℝ) (D : ℕ) : Prop :=
  ∀ {I : Type} (data : I → Packet), (∀ i, 0 < (data i).width) →
    (∀ i, (data i).geometry.wing = 0 ∨ (size (data i).geometry.header+1)^D ≤ (data i).width) →
    ClosedRuns c (fun i => ⌈((data i).volume:ℝ)*(((data i).geometry.wing+1:ℕ):ℝ)^ρ⌉₊)
      (Packet.volume ∘ data) (Packet.input ∘ data) (Packet.output ∘ data)

end PhysicalWalshCompileRect

end NearSquareRoot
end Computability
end OAI
