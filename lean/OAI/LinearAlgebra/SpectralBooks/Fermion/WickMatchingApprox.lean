import OAI.LinearAlgebra.SpectralBooks.Fermion.WickMatchingProduct
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickContractionApprox

/-!
# Laurent approximations for individual Wick matchings

Reversing the block order changes the sign of every scalar contraction.
After accounting for those signs, the forward and reverse kernels have the
same pole order and numerator. The estimate holds at every fixed coefficient
once the mode cutoff is sufficiently large.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion.Matching

theorem weightPoleApprox (rev : Bool) (l r : List FieldLabel) (p : Matching l r)
    (hl : ∀ f ∈ l, f.1 = false) (hr : ∀ g ∈ r, g.1 = true) :
    PoleApprox rev (p.poleOrder Prod.snd) (p.weight (fun x y ↦ kernelNumerator x.2 y.2))
      (fun N ↦ p.weight (fun x y ↦ if rev then -contractionPolynomial N y x
        else contractionPolynomial N x y)) := by
  apply weight_product_estimate Prod.snd (PoleApprox rev) (PoleApprox.constant rev)
    (fun h g ↦ PoleApprox.mul h g)
  intro x hx y hy
  have hxy := poleApprox_contractionPolynomial rev x.2 y.2
  obtain ⟨side, i⟩ := x
  obtain ⟨other, j⟩ := y
  have hs : side = false := hl _ hx
  have ht : other = true := hr _ hy
  subst side other
  exact hxy

end Fermion.Matching

end SpectralBooks
end LinearAlgebra
end OAI
