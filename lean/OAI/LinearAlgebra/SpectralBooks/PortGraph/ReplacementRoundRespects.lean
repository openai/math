import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundMap
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundTransport

/-! # The forward replacement respects decorated map classes -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ShapeCatalogue

open ReplacementTemplate ReplacementChoices UniformDecorations
variable {F : Type} [Field F] {N K w c a h : ℕ} {ε : ℝ}
    (C : ShapeCatalogue F K w c) (S : System N K ε) (ha : 0 < a)
    (hε : ε = 1 / (2 * (a : ℝ))) (code : RoleLabel (C.templates (N:=N) (ε:=ε)) ↪ Bits h)

/-- Each rooted, numbered map isomorphism transporting the old term choices
preserves the full set of encoded labels on the resulting smaller maps. -/
theorem forward_respects (x y : (S.family C.Index).Rep) (hxy : (S.family C.Index).IsIso x y) :
    ((C.rules N ε).acceptedFamily code C.coefficient (max 1 (N/a))).IsIso
      (C.forwardRep S ha hε code x) (C.forwardRep S ha hε code y) := by
  obtain ⟨f,move⟩ := hxy
  exact C.forward_accepted_iso S x.2 y.2 f move code _ _ _ _

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
