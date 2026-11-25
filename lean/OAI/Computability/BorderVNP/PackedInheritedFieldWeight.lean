import OAI.Computability.BorderVNP.FiniteCellEntries

/-! # Field interpretation of a sparse site's local observations

Successful factor observations contribute their joint sign and one scalar for
each selected gadget position. This uses the field product in the cell entry
processor's evaluation formula.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

/-- Field interpretation of a successful sequence of local box observations. -/
def fieldWeight {K : Type*} [Field K] (values : ℕ → K) (obs : List (Bool × Option ℕ)) : K :=
  (if (obs.map Prod.fst).foldl Bool.xor false then -1 else 1) * ((obs.filterMap Prod.snd).map values).prod

end Packing.Inherited

end BorderVNP
end Computability
end OAI
