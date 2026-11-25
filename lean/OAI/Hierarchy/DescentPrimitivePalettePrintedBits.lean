import OAI.Hierarchy.DescentPrimitivePaletteCounts

namespace OAI
/-! # Width of the one-based coefficient word in the fixed primitive dictionary -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (s Z : ℕ) (op : RotorSpec)

/-- One reserved zero and all entries of the unchanged global coefficient dictionary. -/
def printedBits := Nat.clog 2 (colors G s Z op+1)

end
end Hierarchy.DescentPrimitivePalette

end OAI
