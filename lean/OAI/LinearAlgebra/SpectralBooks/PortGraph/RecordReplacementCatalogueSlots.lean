import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementCatalogue
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementForwardMap

/-! # Agreement of the forward and local port tests on the record catalogue -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ShapeCatalogue

open ReplacementTemplate

variable {F : Type} [Field F] {K w c N : ℕ} {ε : ℝ} (C : ShapeCatalogue F K w c)

/-- Consecutive port numbers at each role of the chosen tree term. -/
def portOrder : Forward.PortOrder (C.templates (N:=N) (ε:=ε)) :=
  fun j v => (C.selected j).numbering v

theorem degree (j : C.Tag N ε) (v : (C.templates j).Role) :
    Fintype.card (LocalPort (C.templates j) v) ≤ 3 :=
  ((Fintype.card_congr ((C.selected j).slotEquiv v)).trans (Fintype.card_fin _)).le.trans
    (C.selected j).arity_le_three

/-- The role encoder and the locally checked four-slot lookup use identical
numbers for every incidence, including each end of a parallel edge or loop. -/
theorem rules_slot :
    (C.rules N ε).slot = Forward.slotOfOrders (T:=C.templates) C.portOrder C.degree := by
  funext a
  apply Function.Embedding.ext
  intro p
  apply Fin.ext
  rfl

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
