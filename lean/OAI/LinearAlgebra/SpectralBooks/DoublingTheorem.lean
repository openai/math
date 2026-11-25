import OAI.LinearAlgebra.SpectralBooks.GroupedDoubling
import OAI.LinearAlgebra.SpectralBooks.WireCollapse

/-! # Doubling a spectral price over every field -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor.BookFactors

/-- The manuscript's doubling theorem. The finite site set consists of a
common site, two nonempty private families, and arbitrary auxiliary sites.
The two collapse conditions are zero prices of the ordinary binary wires.

The selected spectral price satisfies a global upper bound on every nonzero
tensor, with equality on every tensor private to either family and on the
binary diagonal of the union. -/
theorem doubling {K : Type*} [Field K] {B C O : Type} [Fintype B] [Fintype C] [Fintype O]
    [Nonempty B] [Nonempty C]
    (a b c : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ)
    (ha : IsSpectralPrice unit_le_nonzeroClass a)
    (hb : IsSpectralPrice unit_le_nonzeroClass b)
    (hc : IsSpectralPrice unit_le_nonzeroClass c)
    (hbc : WireCollapseC b)
    (hagB : ∀ p : PrivateData K B, b (p.left O C) = a (p.left O C))
    (hcb : WireCollapseB c)
    (hagC : ∀ q : PrivateData K C, c (q.right O B) = a (q.right O B))
    (hD : a (jointDiagonal K B C O) = a ((privateDiagonal K B).left O C))
    (hpos : 0 < a ((privateDiagonal K B).left O C))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ g : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ, IsSpectralPrice unit_le_nonzeroClass g ∧
      (∀ t, g t ≤ (lam • a + b + c) t) ∧
      (∀ p : PrivateData K B, g (p.left O C) = (lam • a + b + c) (p.left O C)) ∧
      (∀ q : PrivateData K C, g (q.right O B) = (lam • a + b + c) (q.right O B)) ∧
      g (jointDiagonal K B C O) = (lam • a + b + c) (jointDiagonal K B C O) :=
  doubling_of_grouped_prices a b c ha hb hc (wireCollapseC_monoGroupedC b hb hbc)
    (wireCollapseB_monoGroupedB c hc hcb) hagB hagC hD hpos lam hlam

end SiteTensor.BookFactors

end SpectralBooks
end LinearAlgebra
end OAI
