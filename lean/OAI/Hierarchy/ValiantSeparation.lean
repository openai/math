import OAI.Computability.VPVNP.ClassSeparation
import OAI.Hierarchy.Valiant
import OAI.Hierarchy.WitnessSum

namespace OAI
namespace Hierarchy
namespace Valiant

open Computability.VPVNP.Valiant.Project

/-- The established VP–VNP separation also separates the bundled classes of families. -/
theorem vp_ssubset_vnp (F : Type*) [Field F] : VP F ⊂ VNP F := by
  have incl : VP F ⊆ VNP F := by
    intro p hp
    exact (isVNP_iff p.polynomials).mpr (isVNP_of_isVP ((isVP_iff p.polynomials).mp hp))
  refine ⟨incl, fun rev => Computability.VPVNP.Standalone.vp_ne_vnp F ?_⟩
  funext f
  apply propext
  let p := PolynomialFamily.ofFamily f
  exact ⟨fun hp => incl (show p ∈ VP F from hp), fun hv => rev (show p ∈ VNP F from hv)⟩

end Valiant
end Hierarchy
end OAI
