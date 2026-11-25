import OAI.Hierarchy.DescentRelativeThreshold
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Four short thresholds determine the relative rank of a shape -/
namespace Hierarchy.DescentRelativeClassChip
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {field : ℕ}

def rank (x : Fin 5→Cell field) : Cell field :=
  ((Finset.univ.filter (fun j : Fin 4=>earlier (x j.castSucc).val (x 4).val)).card:ℕ)

end
end Hierarchy.DescentRelativeClassChip

end OAI
