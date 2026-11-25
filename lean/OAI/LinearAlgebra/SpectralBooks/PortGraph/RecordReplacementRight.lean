import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementRightIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundMap

/-! # The right inverse on accepted finite map representatives -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ShapeCatalogue
open ReplacementChoices ReplacementTemplate UniformDecorations

variable {F : Type} [Field F] {N K w c : ℕ} {ε : ℝ} (C : ShapeCatalogue F K w c)
  (S : System N K ε)

variable {a h : ℕ} (ha : 0 < a) (hε : ε = 1 / (2 * (a : ℝ)))
  (code : RoleLabel (C.templates (N:=N) (ε:=ε)) ↪ Bits h)

/-- Reverse-then-forward is the identity on the actual accepted family up to
a rooted, port-numbered, role-preserving isomorphism of finite representatives. -/
theorem right_inverse (q : ((C.rules N ε).acceptedFamily code C.coefficient (max 1 (N/a))).Rep) :
    ((C.rules N ε).acceptedFamily code C.coefficient (max 1 (N/a))).IsIso
      (C.forwardRep S ha hε code (C.reverse S code q)) q :=
  let t := C.reverse S code q
  (C.rules N ε).acceptedRep_isIso code C.coefficient (C.forwardMap S t.1 t.2)
    (C.forward_cap S t.1 t.2 ha hε) (C.forward_spherical S t.1 t.2)
    (C.forwardLabel S t.1 t.2) (C.forward_accepts S t.1 t.2) q
    (C.rightMapIso S q.1.map q.2.val q.2.property) (C.rightMapIso_label S q.1.map q.2.val q.2.property)

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
