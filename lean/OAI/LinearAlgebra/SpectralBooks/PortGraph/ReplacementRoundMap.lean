import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundSpherical
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAcceptedRep

/-! # The certified map produced by a round of replacement -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ShapeCatalogue

open ReplacementChoices ReplacementTemplate UniformDecorations
variable {F : Type} [Field F] {N K w c : ℕ} {ε : ℝ} (C : ShapeCatalogue F K w c)
    (S : System N K ε) (M : MapRep N) (t : (S.family C.Index).Label M)

variable {a h : ℕ} (ha : 0 < a) (hε : ε = 1 / (2 * (a : ℝ)))
  (code : RoleLabel (C.templates (N:=N) (ε:=ε)) ↪ Bits h)

/-- Forward replacement as a finite representative of the decorated smaller
map, with every term index encoded in its role. -/
def forwardRep (q : (S.family C.Index).Rep) :
    ((C.rules N ε).acceptedFamily code C.coefficient (max 1 (N/a))).Rep :=
  (C.rules N ε).acceptedRep code C.coefficient (C.forwardMap S q.1 q.2)
    (C.forward_cap S q.1 q.2 ha hε) (C.forward_spherical S q.1 q.2)
    (C.forwardLabel S q.1 q.2) (C.forward_accepts S q.1 q.2)

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
