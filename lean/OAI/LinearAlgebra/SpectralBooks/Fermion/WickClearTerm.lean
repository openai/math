import OAI.LinearAlgebra.SpectralBooks.Fermion.WickClearMatching
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickMatchingApprox

/-! # Cancellation of individual forward and reverse fermionic contractions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

open LaurentPolynomial Filter

/-- After coefficientwise stabilization and clearing, exactly the full matchings
remain. Their integral numerators multiply the identity on the input state. -/
theorem Matching.eventually_clear_term {l r : List FieldLabel} (p : Matching l r)
    (hlen : l.length = r.length) (hne : l ≠ [])
    (hl : ∀ f ∈ l, f.1 = false) (hr : ∀ g ∈ r, g.1 = true) (α β : State) (s : ℤ) :
    let L := order (wordWeight Prod.snd l) (wordWeight Prod.snd r)
    let P := mixedNormal p.residual α β
    ∀ᶠ N in atTop, ((1-T 1)^L * (p.weight (contractionPolynomial N) * P)).coeff s -
      ((1-T 1)^L * (p.weight (fun x y => -contractionPolynomial N y x) * P)).coeff s =
      if p.residual = [] then p.weight (fun x y => kernelNumerator x.2 y.2) *
        (if α = β then 1 else 0) else 0 := by
  apply p.eventually_clear_of_coeff hlen hne
  · intro t
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      (Matching.weightPoleApprox false l r p hl hr).coeff t
  · intro t
    simpa only [↓reduceIte] using (Matching.weightPoleApprox true l r p hl hr).coeff t

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
