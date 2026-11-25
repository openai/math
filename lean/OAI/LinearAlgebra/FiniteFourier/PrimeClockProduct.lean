import Mathlib

/-! # Products around a cyclic clock -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Fin.NatCast

variable {R : Type*} {b : ℕ} [NeZero b]

/-- Starting at any clock position visits every label exactly once. -/
theorem prod_clock_shift [CommMonoid R] (v : Fin b → R) (r : Fin b) :
    ∏ k ∈ Finset.range b, v (r + (k : Fin b)) = ∏ t, v t := by
  rw [← Fin.prod_univ_eq_prod_range]
  simpa using Equiv.prod_comp (Equiv.addLeft r) v

/-- Multiplication by a `b`-th root of unity increments its clock exponent. -/
theorem pow_clock_succ [Monoid R] (ξ : R) (hξ : ξ ^ b = 1) (r : Fin b) :
    ξ ^ (r + 1 : Fin b).val = ξ * ξ ^ r.val := by
  rw [← pow_succ']
  have hmod : (r + 1 : Fin b).val = (r.val + 1) % b := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hmod]
  conv_rhs => rw [← Nat.mod_add_div (r.val + 1) b, pow_add, pow_mul, hξ, one_pow, mul_one]

end FiniteFourier
end LinearAlgebra
end OAI
