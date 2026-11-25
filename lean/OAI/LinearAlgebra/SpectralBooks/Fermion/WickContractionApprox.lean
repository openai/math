import OAI.LinearAlgebra.SpectralBooks.Fermion.WickApproximation
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickContractionForward
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickContractionReverse

/-! # Pole approximation for a single contraction

At $(1,X)$ the forward contraction and the negative reversed contraction
give the two Laurent expansions of the same differentiated propagator.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

/-- Both orientations of the finite-mode contraction approximate the pole
of order `i+j+1` and numerator `kernelNumerator i j`. -/
theorem poleApprox_contractionPolynomial (rev : Bool) (i j : ℕ) :
    PoleApprox rev (i+j+1) (kernelNumerator i j)
      (fun N ↦ if rev then -contractionPolynomial N (true,j) (false,i)
        else contractionPolynomial N (false,i) (true,j)) := by
  cases rev
  · simpa only [Bool.false_eq_true, ite_false, contractionPolynomial_forward, trimPole] using
      PoleApprox.trim false (i+j+1) (kernelNumerator i j) j
  · simpa only [ite_true, neg_contractionPolynomial_reverse, trimPole, Nat.cast_add, Nat.cast_one,
      sub_add_eq_sub_sub] using PoleApprox.trim true (i+j+1) (kernelNumerator i j) i

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
