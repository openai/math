import OAI.LinearAlgebra.SpectralBooks.Fermion.WickPoles
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Products of scalar contractions in a partial Wick matching

A multiplicative estimate for an individual pair extends to any signed
matching. The pole orders add. The numerator includes the permutation signs
from the positions of the two fields that are contracted.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion.Matching

open LaurentPolynomial
noncomputable section

/-- Lift a multiplicative scalar-kernel estimate to the signed weight of a
matching. Constant Laurent polynomials have order zero. -/
theorem weight_product_estimate {α : Type*} (mode : α → ℕ)
    (R : ℕ → ℤ → (ℕ → LaurentPolynomial ℤ) → Prop)
    (hC : ∀ c, R 0 c (fun _ ↦ C c))
    (hmul : ∀ {i j c d f g}, R i c f → R j d g → R (i+j) (c*d) (fun N ↦ f N * g N))
    (num : α → α → ℤ) (kern : ℕ → α → α → LaurentPolynomial ℤ)
    (l r : List α) (p : Matching l r)
    (hatom : ∀ x ∈ l, ∀ y ∈ r, R (mode x + mode y + 1) (num x y) (fun N ↦ kern N x y)) :
    R (p.poleOrder mode) (p.weight num) (fun N ↦ p.weight (kern N)) := by
  induction l generalizing r with
  | nil => simpa [poleOrder, weight] using hC 1
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · exact ih _ p (fun y hy ↦ hatom y (List.mem_cons_of_mem _ hy))
    · have htail := ih _ p (fun y hy z hz ↦
        hatom y (List.mem_cons_of_mem _ hy) z (List.mem_of_mem_eraseIdx hz))
      have hpair := hatom x List.mem_cons_self _ (List.getElem_mem j.isLt)
      have hsign := hC (((-1:ℤ)^l.length) * ((-1:ℤ)^j.val))
      have hprod := hmul (hmul hsign hpair) htail
      simpa only [poleOrder, weight, Nat.zero_add, map_mul, map_pow, map_neg, map_one,
        mul_assoc] using hprod

end
end Fermion.Matching

end SpectralBooks
end LinearAlgebra
end OAI
