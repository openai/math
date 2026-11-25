import OAI.LinearAlgebra.SpectralBooks.Fermion.WickFinite
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickNormalMatrix
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickPoles
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickPairing

/-! # Summation of the cleared matching coefficients -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Filter LaurentPolynomial
open scoped BigOperators

/-- The energy of the tagged, sorted list agrees with the state's energy. -/
theorem wordWeight_fieldWord (i : State) (b : Bool) :
    wordWeight Prod.snd (fieldWord b i) = weight i := by
  simp only [wordWeight, fieldWord, List.map_map]
  change (Multiset.map (fun t : ℕ ↦ 2*t+1) (i.sort (· ≤ ·) : Multiset ℕ)).sum = _
  rw [Finset.sort_eq]
  rfl

/-- Sum the stabilized matching coefficients. There are finitely many matchings,
and the completely contracted ones sum to the Pascal determinant. -/
theorem eventually_cleared_wick_sum (i j α β : State) (hij : i.card = j.card)
    (s : ℤ) (L : ℕ)
    (hterm : ∀ p : Matching (fieldWord false i) (fieldWord true j),
      ∀ᶠ N : ℕ in atTop,
        ((1 - T 1)^L * (p.weight (contractionPolynomial N) * mixedNormal p.residual α β)).coeff s -
        ((1 - T 1)^L * (p.weight (fun f g ↦ -(contractionPolynomial N g f)) *
          mixedNormal p.residual α β)).coeff s =
        (if p.residual.isEmpty then p.weight (fun f g ↦ kernelNumerator f.2 g.2) else 0) *
          (if α = β then 1 else 0)) :
    ∀ᶠ N : ℕ in atTop,
      ((1 - T 1)^L * (∑ p : Matching (fieldWord false i) (fieldWord true j),
        (p.weight (contractionPolynomial N) - p.weight (fun f g ↦ -(contractionPolynomial N g f))) *
          mixedNormal p.residual α β)).coeff s = pairing i j * (if α = β then 1 else 0) := by
  filter_upwards [eventually_all.mpr hterm] with N hN
  rw [← fullContractions_tagged_kernelNumerator i j hij.symm false true]
  simp only [fullContractions, Finset.sum_mul, Finset.mul_sum, sub_mul, mul_sub,
    AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_sub, Finsupp.finsetSum_apply, Finsupp.sub_apply]
  exact Finset.sum_congr rfl (fun p _ ↦ hN p)

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
