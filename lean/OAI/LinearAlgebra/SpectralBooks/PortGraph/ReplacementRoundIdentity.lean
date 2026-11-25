import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundRespects
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementLeft
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementRight
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementWeight
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoiceWeights
import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.GridUniversalPolynomial

/-! # The replacement identity for the universal spherical-map polynomial

A term is counted once for each list position on each canonical patch of
the old map. Reversing a passing decoration, with its numbered half-edges,
gives the inverse on rooted isomorphism classes.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped BigOperators Classical

namespace PortGraph.ShapeCatalogue
open ReplacementTemplate ReplacementChoices UniformDecorations

variable {F : Type} [Field F] {N K w c a h : ℕ} {ε : ℝ}
    (C : ShapeCatalogue F K w c) (S : System N K ε) (ha : 0 < a)
    (hε : ε = 1 / (2 * (a : ℝ))) (code : RoleLabel (C.templates (N:=N) (ε:=ε)) ↪ Bits h)

/-- One actual, passing decorated map up to numbered rooted isomorphism for
each old map up to isomorphism equipped with its chosen term indices. -/
def classEquiv : (S.family C.Index).Class ≃
    ((C.rules N ε).acceptedFamily code C.coefficient (max 1 (N/a))).Class :=
  (S.family C.Index).equivOfIsoForwardInverse _
    (C.forwardRep S ha hε code) (C.reverse S code) (C.forward_respects S ha hε code)
    (C.reverse_respects S code) (C.reverse_forward S ha hε code) (C.right_inverse S ha hε code)

include S ha hε in
/-- Exact one-round equality on independent indeterminates representing all
entries in the old tables. It works in arbitrary field characteristic. -/
theorem Zpoly_eq_acceptedWeight :
    Zpoly N w = ∑ x : ((C.rules N ε).acceptedFamily code C.coefficient (max 1 (N/a))).Class,
      (C.rules N ε).acceptedWeight code C.coefficient x := by
  have expanded := S.Z_eq_sum_choices C.Index C.termValue (PatchShape.RecordTerm.worldTable F w)
    (fun r x => C.sum_value r.val.shape r.property.connected x)
  refine expanded.trans ?_
  let e := (S.family C.Index).choicesEquivClass.trans (C.classEquiv S ha hε code)
  refine Fintype.sum_equiv e _ _ ?_
  intro q
  let x : (S.family C.Index).Rep := ⟨q.1.out,q.2⟩
  change _ = (C.rules N ε).acceptedWeight code C.coefficient
    (((C.rules N ε).acceptedFamily code C.coefficient (max 1 (N/a))).classOf
      (C.forwardRep S ha hε code x))
  symm
  refine ((C.rules N ε).acceptedRep_weight code C.coefficient (C.forwardMap S x.1 x.2)
    (C.forward_cap S x.1 x.2 ha hε) (C.forward_spherical S x.1 x.2)
    (C.forwardLabel S x.1 x.2) (C.forward_accepts S x.1 x.2)).trans ?_
  exact C.forwardWeight_eq_choiceValue S x.1 x.2

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
