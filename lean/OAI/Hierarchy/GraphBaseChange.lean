import OAI.Hierarchy.CircuitBorderExtension
import OAI.Hierarchy.ModelBorderExtension

namespace OAI
/-! # Field extension for independent vertex-table contractions -/

namespace Hierarchy.IncidenceGraph

open MvPolynomial

variable (G : IncidenceGraph) (F E : Type*) [Field F] [Field E] [Algebra F E]

theorem abp_border_baseChange (q s : ℕ) :
    DegreeBorderAtMost HasABP (Fintype.card G.V) s (G.contraction E q) ↔
      DegreeBorderAtMost HasABP (Fintype.card G.V) s (G.contraction F q) := by
  simpa only [G.map_contraction] using
    abpDegreeBorder_map_iff (E := E) (Fintype.card G.V) s (G.contraction F q)

theorem formula_border_baseChange (q s : ℕ) :
    DegreeBorderAtMost HasFormula (Fintype.card G.V) s (G.contraction E q) ↔
      DegreeBorderAtMost HasFormula (Fintype.card G.V) s (G.contraction F q) := by
  simpa only [G.map_contraction] using
    formulaDegreeBorder_map_iff (E := E) (Fintype.card G.V) s (G.contraction F q)

end Hierarchy.IncidenceGraph

end OAI
