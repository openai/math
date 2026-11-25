import OAI.Hierarchy.DescentSeedOriginalVertex
import OAI.Hierarchy.DescentSeedTokenPlan
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Fixed addresses of the native packed primitive-role source -/
namespace Hierarchy.DescentPackedSeed.Primitive.Source
open DescentDyadicSpan DescentSeedRoot DescentSIMDLookup ProtocolRAM Catalyst
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (R s payload : ℕ)
local notation "O" => Fintype.card (Old X)
local notation "A" => pieces payload s
def jobs := O*chunks R A
local notation "n" => jobs X R s payload
def raw (base : ℕ) := base+span (cols s A)+2*span n
def finish (base : ℕ) :=raw X R s payload base+span n
def bank (base : ℕ) : Bank :=⟨raw X R s payload base,Nat.clog 2 n⟩
end
end Hierarchy.DescentPackedSeed.Primitive.Source

end OAI
