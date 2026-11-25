import OAI.Computability.BorderVNP.DiagonalEvaluator
import OAI.Computability.BorderVNP.ResidueNumberedExpansion

/-! # Number the actual subtotal words in the same order as the arithmetic branch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open MvPolynomial ParseTable
open scoped BigOperators Classical

variable {Team Team' Param Param' Gadget E : Type*} [Fintype Team] [Fintype Team']
    [Fintype Param] [Fintype Param'] [Fintype Gadget] [Field E] {b : ℕ}

namespace Tally

/-- Relabel both arrays without changing any occurrence. The team map is the
physical row-major enumeration and the parameter map is the chosen numbering
of the actual grammar labels. -/
def renumber (teams : Team ≃ Team') (params : Param ≃ Param')
    (t : Tally Team Param Gadget b) : Tally Team' Param' Gadget b where
  powers i p j := t.powers (teams.symm i) (params.symm p) j
  counts i g := t.counts (teams.symm i) g

omit [Fintype Gadget] in
/-- Numbering sends the formal exponent through the ordinary domain map. -/
theorem renumber_exponents (teams : Team ≃ Team') (params : Param ≃ Param')
    (t : Tally Team Param Gadget b) :
    (t.renumber teams params).exponents = t.exponents.mapDomain params := by
  simp only [exponents, Finsupp.mapDomain_finsetSum, batchExponent, Finsupp.mapDomain_single]
  apply Fintype.sum_equiv teams.symm
  intro i
  apply Fintype.sum_equiv params.symm
  intro p
  simp only [renumber, Equiv.apply_symm_apply]
  rfl

omit [Fintype Param] [Fintype Param'] in
/-- Scalar multiplicities use the identical table-position alphabet. -/
theorem renumber_coefficient (teams : Team ≃ Team') (params : Param ≃ Param')
    (t : Tally Team Param Gadget b) (values : Gadget → E) :
    (t.renumber teams params).coefficient values = t.coefficient values := by
  unfold coefficient
  apply Finset.prod_congr rfl
  intro g _
  exact congrArg (fun a : ℕ => values g ^ a) (teams.symm.sum_comp (fun i => t.counts i g))

end Tally

/-- The physical expansion, in the exact team and parameter coordinates
required by the numbered signed branch and the native subtotal reader. -/
theorem numbered_tally_expansion {Pin Wire Proc Path : Type*}
    [Fintype Wire] [Fintype Proc] [Fintype Path] (k s : ℕ)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (teams : Team ≃ Team') (layout : Proc → Fin (k+1) → InputSlot Pin Wire)
    (pins : Pin → Bool) (values : Gadget → E)
    (t : Path → Tally Team (PairedParameters k s) Gadget b)
    (h : substituted E k s layout pins = ∑ j, monomial (t j).exponents ((t j).coefficient values)) :
    numberedSubstituted E k s ord layout pins =
      ∑ j, monomial ((t j).renumber teams (numberedLabelEquiv ord k s)).exponents
        (((t j).renumber teams (numberedLabelEquiv ord k s)).coefficient values) := by
  simp only [Tally.renumber_exponents, Tally.renumber_coefficient]
  exact numberedSubstituted_expand k s ord layout pins _ _ h

end Diagonal

end BorderVNP
end Computability
end OAI
