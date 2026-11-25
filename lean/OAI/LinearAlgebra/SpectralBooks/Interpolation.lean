import Mathlib.LinearAlgebra.Lagrange
import OAI.LinearAlgebra.SpectralBooks.InterpolationSupport

/-!
# Interpolation for the common-label restriction

The coefficient of a prescribed monomial of degree at most `D` is a linear
combination of evaluations at `D + 1` distinct field elements. Applying this
to the monomial obtained by multiplying the local label weights gives a
restriction from a diagonal of dimension `2r(q-1)+1`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators
open Polynomial

section

/-- The weights are independent of the monomial being tested. This allows a
single shared diagonal label to select the evaluation at all sites. -/
theorem exists_monomial_coefficient_weights (F : Type*) [Field F] [Infinite F] (D d : ℕ) :
    ∃ x : Fin (D + 1) ↪ F, ∃ w : Fin (D + 1) → F, ∀ e ≤ D,
      ∑ i, w i * x i ^ e = if e = d then 1 else 0 := by
  classical
  let x : Fin (D + 1) ↪ F := Fin.valEmbedding.trans (Infinite.natEmbedding F)
  refine ⟨x, fun i ↦ (Lagrange.basis Finset.univ x i).coeff d, ?_⟩
  intro e he
  have hdeg : (X ^ e : F[X]).degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    rw [degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le he
  have h := congrArg (fun f : F[X] ↦ f.coeff d) (Lagrange.eq_interpolate x.injective.injOn hdeg)
  simp only [Lagrange.interpolate_apply, finsetSum_coeff, coeff_C_mul, eval_pow, eval_X,
    coeff_X_pow] at h
  simpa only [mul_comm, eq_comm] using h.symm

/-- The shared evaluation label implements the equation from the proof of
intersecting submodularity. The three factors on the left are respectively
local to the first site, the other `k` sites of the intersection, and the
new site. The equation on the right is an equality of integers in every
field characteristic. -/
theorem exists_equation_restriction (F : Type*) [Field F] [Infinite F] (q k : ℕ) :
    ∃ x : Fin (2 * (k + 1) * (q - 1) + 1) ↪ F,
      ∃ w : Fin (2 * (k + 1) * (q - 1) + 1) → F,
        ∀ (h g a : Fin q) (v : Fin k → Fin q),
          ∑ l, (w l * x l ^ (q - 1 - h.val + k * a.val)) *
              (∏ j, x l ^ (q - 1 - (v j).val)) * x l ^ g.val =
            if (g.val : ℤ) = h.val + (∑ j, ((v j).val : ℤ)) - (k : ℤ) * a.val then 1 else 0 := by
  obtain ⟨x, w, hw⟩ := exists_monomial_coefficient_weights F (2 * (k + 1) * (q - 1))
    ((k + 1) * (q - 1))
  refine ⟨x, w, fun h g a v ↦ ?_⟩
  simp only [← supportExponent_eq_iff h g a v]
  rw [← hw _ (supportExponent_le h g a v)]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [supportExponent, pow_add, mul_assoc]

end

end SpectralBooks
end LinearAlgebra
end OAI
