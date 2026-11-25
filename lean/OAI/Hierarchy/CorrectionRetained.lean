import OAI.Hierarchy.Catalyst
import OAI.Hierarchy.SparseCorrection

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace Hierarchy.CorrectionAssembly
variable {F : Type*} [Field F] {k p s : ℕ}

/-- The finite subset expansion used by sparse amplification. -/
def retained (X : Catalyst.Approximation F k p) (f : (Fin p → Bool) → F)
    (L : ℕ) (x : (Fin s × Catalyst.Port p X.width) → Bool) : F :=
  ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin s) => J.card ≤ L),
    SparseCorrection.term
      (fun i => Catalyst.ideal X.width f (fun j => x (i,j)) - X.coeff (fun j => x (i,j)))
      (fun i => X.coeff (fun j => x (i,j))) J

end Hierarchy.CorrectionAssembly

end
end OAI
