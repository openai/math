import OAI.LinearAlgebra.MatrixExponent.Rectangle
import OAI.LinearAlgebra.MatrixExponent.Routing.Square
import OAI.LinearAlgebra.MatrixExponent.Routing.Dual
import OAI.LinearAlgebra.MatrixExponent.Tagged.Reduction
import OAI.LinearAlgebra.MatrixExponent.Iteration
import OAI.LinearAlgebra.MatrixExponent.Shaving.Network

/-!
# The two alternatives on the spectral space

Failure of shared pricing forces contact on a tripod. Shared pricing
supplies both kinds of sorting and local concentration. Two network
estimates over prime fields would exclude this second alternative.
-/

namespace OAI.LinearAlgebra.MatrixExponent

/-- Square equality and rectangular rigidity follow simultaneously. -/
theorem contact_of_network_estimates
    (hard : ∀ (p : ℕ) [Fact p.Prime], Tagged.Hard (ZMod p))
    (stage : ∀ (p : ℕ) [Fact p.Prime], Prices.SharedPrice (AlgebraicClosure (ZMod p)) →
      ArityReduction (ZMod p))
    (F : Type*) [Field F] : omega F = 9 / 4 ∧ Rectangle.Rigidity F := by
  apply Rectangle.of_prime_fields _ F
  intro p _
  apply contact_of_not_shared
  intro sync
  obtain ⟨q, hq, hq', sort⟩ := Routing.sorting_of_shared_price sync
  have shrink := compresses_of_stages hq hq' sort (stage p sync)
  exact incompatible (seed _) (Tagged.manyList_of_tag (hard p)) shrink.lists

end OAI.LinearAlgebra.MatrixExponent
