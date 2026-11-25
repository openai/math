import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # The four short words of an original candidate for a reset source ticket -/
namespace Hierarchy.DescentResetSourceTicketRAM
open DescentSIMDLookup
noncomputable section
variable {K bits : ℕ}

abbrev Fields (K bits : ℕ) := Fin (K*4)→Cell bits

def field (x : Fields K bits) (j : Fin K) (i : Fin 4) : ℕ := (x (finProdFinEquiv (j,i))).val

/-- The source of the query is fixed; all earlier grains incident at this
source contribute. A parent whose two ends agree appears just once. -/
def fee (x : Fields K bits) (query j : Fin K) : ℕ :=
  if (field x j 0=field x query 0 ∨ field x j 1=field x query 0) ∧ field x j 2<field x query 2
  then field x j 3 else 0

end
end Hierarchy.DescentResetSourceTicketRAM

end OAI
