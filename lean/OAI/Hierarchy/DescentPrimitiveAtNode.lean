import OAI.Hierarchy.DescentOriginalPaletteEncoding

namespace OAI
/-! # The coefficient token of an indexed node in the original bit recipe -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty
variable {F U P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {read : U→List (List Bool)→F}
def Encoding.atNode {B : BitDescription W} (e : Encoding U read B) (x : NodeOrder.All B) : U :=
  e.code ((B.recipe x.1).tag x.2)
end Hierarchy.DescentPrimitivePalette

end OAI
