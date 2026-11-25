import OAI.Computability.BorderVNP.DiagonalPhysicalAssignments

/-! # Numbered rows read from the fully assigned compression terms -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Assigned

open Crossing MvPolynomial ParseTable BorderVNP.Cube
open scoped Classical BigOperators

variable {D n d b h K s exp k size : ℕ}
    {Team Team' Gadget E History Hidden Pin PhysicalPin Wire Proc : Type}
    [Fintype Team] [Fintype Team'] [Fintype Gadget] [Field E]
    [Fintype History] [Fintype Hidden] [Fintype Wire] [Fintype Proc]
    {Port : History → Type} {width : (q : History) → Port q → ℕ}
    (N : (q : History) → Network D (Port q) (width q))
    (packet : ∀ q, PacketPlacement Team n d b h K (N q))
    (tags : ∀ q, Hidden → Tracked Team (PairedParameters k size) Gadget exp (N q))
    (pin : Pin → ∀ q, Ports (width q)) (pos : TableEntry n b h K s → Gadget)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (teams : Team ≃ Team')

/-- The exponent and scalar multiplicity arrays of the numbered arithmetic
branch for this particular passing physical assignment. -/
noncomputable def numbered (i : Pin) (a : Path N packet tags pin pos i) :=
  (term N packet tags pin pos i a).renumber teams (numberedLabelEquiv ord k size)

/-- Substitute the exterior-sewn compression expansion into the numbered
parse row. The summation uses the actual accepting bit assignments, with
independent private bottom choices and all packet coordinates. -/
theorem numbered_row (layout : Proc → Fin (k+1) → InputSlot PhysicalPin Wire)
    (encode : Pin → PhysicalPin → Bool) (values : Gadget → E) (valid : ValidTables (values ∘ pos))
    (i : Pin) (sewn : substituted E k size layout (encode i) =
      ∑ q, ∑ z, ((tags q z).valued values).tensor (pin i q)) :
    numberedSubstituted E k size ord layout (encode i) =
      ∑ a : Path N packet tags pin pos i, monomial
        (numbered N packet tags pin pos ord teams i a).exponents
        ((numbered N packet tags pin pos ord teams i a).coefficient values) :=
  numbered_tally_expansion k size ord teams layout (encode i) values (term N packet tags pin pos i)
    (sewn.trans (sum_terms N packet tags pin pos values valid i))

end Diagonal.CellEntries.Assigned

end BorderVNP
end Computability
end OAI
