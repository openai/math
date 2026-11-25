import OAI.Computability.BorderVNP.ResidueNumberedQuery
import OAI.Computability.BorderVNP.ResidueParseReindex

/-!
# Relabeling the assigned terms of a substituted row

The production labels read by the physical network and the numbers read by the
residue evaluator index the same coefficient parameters. Numbering a complete
expansion preserves its weights and sends each exponent vector to the
correspondingly numbered exponent vector, including repeated occurrences.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open MvPolynomial Branch ParseTable
open scoped BigOperators Classical

variable {Pin Wire Proc : Type*} [Fintype Wire] [Fintype Proc]
variable {E : Type*} [Field E]

/-- The numbered contraction used at the geometric branch is precisely the relabeling
of the signed diagonal's substituted polynomial. -/
theorem numberedSubstituted_eq_rename (k s : ℕ) (e : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (pins : Pin → Bool) :
    numberedSubstituted E k s e layout pins = rename (numberedLabelEquiv e k s)
      (substituted E k s layout pins) := by
  have hm (μ : DegreeMonomial (Fin (k+1) × Bool) (k+1)) :
      numberedMonomial e μ = degreeEquiv e (k+1) μ :=
    Subtype.ext (degreeEquiv_val e μ).symm
  simp only [numberedSubstituted, substituted, map_sum, map_prod, hm, numberedTable_reindex]

/-- Any assignment expansion of the physical row yields the same assignment
expansion on the numbered variables after mapping every multiplicity vector. -/
theorem numberedSubstituted_expand {Path : Type*} [Fintype Path] (k s : ℕ)
    (e : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (pins : Pin → Bool)
    (μ : Path → PairedParameters k s →₀ ℕ) (a : Path → E)
    (hex : substituted E k s layout pins = ∑ i, monomial (μ i) (a i)) :
    numberedSubstituted E k s e layout pins =
      ∑ i, monomial ((μ i).mapDomain (numberedLabelEquiv e k s)) (a i) := by
  rw [numberedSubstituted_eq_rename, hex, map_sum]
  simp only [rename_monomial]

end Diagonal

end BorderVNP
end Computability
end OAI
