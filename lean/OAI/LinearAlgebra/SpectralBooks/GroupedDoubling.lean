import OAI.LinearAlgebra.SpectralBooks.GroundFieldComparison
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.StretchSpectral

/-! # Doubling after identifying the collapsed sites -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor.BookFactors

open SitePriceEval

variable {K : Type*} [Field K] {B C O : Type} [Fintype B] [Fintype C] [Fintype O]

/-- Doubling over any field for placements at which grouped-site linear maps
preserve restriction monotonicity. The price bound applies on all sites,
including the auxiliary sites `O`. -/
theorem doubling_of_grouped_prices
    (a b c : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ)
    (ha : IsSpectralPrice unit_le_nonzeroClass a)
    (hb : IsSpectralPrice unit_le_nonzeroClass b)
    (hc : IsSpectralPrice unit_le_nonzeroClass c)
    (hbc : (ofSupportedClassPrice b hb).MonoGroupedC)
    (hcb : (ofSupportedClassPrice c hc).MonoGroupedB)
    (hagB : ∀ p : PrivateData K B, b (p.left O C) = a (p.left O C))
    (hagC : ∀ q : PrivateData K C, c (q.right O B) = a (q.right O B))
    (hD : a (jointDiagonal K B C O) = a ((privateDiagonal K B).left O C))
    (hpos : 0 < a ((privateDiagonal K B).left O C))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ g : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ, IsSpectralPrice unit_le_nonzeroClass g ∧
      (∀ t, g t ≤ (lam • a + b + c) t) ∧
      (∀ p : PrivateData K B, g (p.left O C) = (lam • a + b + c) (p.left O C)) ∧
      (∀ q : PrivateData K C, g (q.right O B) = (lam • a + b + c) (q.right O B)) ∧
      g (jointDiagonal K B C O) = (lam • a + b + c) (jointDiagonal K B C O) :=
  doubling_of_class_stretch (strictSpectralComparison _ _) a b c ha hb hc lam hlam hpos (hagB _)
    (fun _ p q Z hs => ClassOrdinarySum.stretch ha hb hc hlam hbc hcb hagB hagC hD p q Z hs)

end SiteTensor.BookFactors

end SpectralBooks
end LinearAlgebra
end OAI
