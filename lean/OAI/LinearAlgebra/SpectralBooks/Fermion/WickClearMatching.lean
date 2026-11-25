import OAI.LinearAlgebra.SpectralBooks.Fermion.WickClear
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickPoles
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickPolynomial

/-! # Coefficients of an individual cleared Wick matching

Both expansion orders have a common normal-ordered residual Laurent polynomial.
A complete matching has the empty residual, whose matrix element is the Kronecker delta.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

open LaurentPolynomial Filter

private theorem sum_empty_residual (α β : State) :
    ∑ t ∈ (mixedNormal [] α β).coeff.support, (mixedNormal [] α β).coeff t =
      (if α = β then 1 else 0) := by
  by_cases h : α = β
  · simp only [mixedNormal, ite_eq_left h, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.support_single _ (one_ne_zero : (1 : ℤ) ≠ 0), Finset.sum_singleton,
      Finsupp.single_eq_same]
  · simp [mixedNormal, h]

/-- Coefficientwise stabilization of the two matching weights suffices for the cleared
matrix entry. The finite pole-order computation distinguishes full and partial matchings. -/
theorem Matching.eventually_clear_of_coeff {l r : List FieldLabel} (p : Matching l r)
    (hlen : l.length = r.length) (hne : l ≠ [])
    (f g : ℕ → LaurentPolynomial ℤ) (a : ℤ)
    (hf : ∀ t, ∀ᶠ N in atTop, (f N).coeff t = a * forwardKernel (p.poleOrder Prod.snd) t)
    (hg : ∀ t, ∀ᶠ N in atTop, (g N).coeff t = a * reverseKernel (p.poleOrder Prod.snd) t)
    (α β : State) (s : ℤ) :
    let L := order (wordWeight Prod.snd l) (wordWeight Prod.snd r)
    let P := mixedNormal p.residual α β
    ∀ᶠ N in atTop, ((1-T 1)^L * (f N * P)).coeff s -
      ((1-T 1)^L * (g N * P)).coeff s =
      if p.residual = [] then a * (if α = β then 1 else 0) else 0 := by
  dsimp only
  by_cases hp : p.residual = []
  · have hk := p.poleOrder_eq_of_residual_nil Prod.snd hlen hne hp
    rw [hk] at hf hg
    simpa only [hp, ite_true, sum_empty_residual] using
      eventually_coeff_clear_full f g a _ hf hg (mixedNormal p.residual α β) s
  · simpa only [ite_eq_right hp] using eventually_coeff_clear_partial f g a _ _
      (p.poleOrder_le_of_residual_ne_nil Prod.snd hlen hp) hf hg (mixedNormal p.residual α β) s

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
