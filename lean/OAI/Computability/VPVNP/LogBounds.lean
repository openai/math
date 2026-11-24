import OAI.Computability.VPVNP.PolynomialBounds
import Mathlib.Data.Nat.Log

/-!
# Polynomial bit-length bounds for natural arithmetic

The binary logarithms of sizes are closed under sums, products, and raising
a size to a polynomially bounded exponent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PolynomiallyBounded

variable {f g : ℕ → ℕ}

theorem clog (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun n => Nat.clog 2 (f n)) :=
  hf.of_le fun _ => Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

theorem clog_mul (hf : PolynomiallyBounded (fun n => Nat.clog 2 (f n)))
    (hg : PolynomiallyBounded (fun n => Nat.clog 2 (g n))) :
    PolynomiallyBounded (fun n => Nat.clog 2 (f n * g n)) := by
  refine (hf.add hg).of_le fun n => Nat.clog_le_of_le_pow ?_
  change f n * g n ≤ 2 ^ (Nat.clog 2 (f n) + Nat.clog 2 (g n))
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)

theorem clog_add (hf : PolynomiallyBounded (fun n => Nat.clog 2 (f n)))
    (hg : PolynomiallyBounded (fun n => Nat.clog 2 (g n))) :
    PolynomiallyBounded (fun n => Nat.clog 2 (f n + g n)) := by
  refine ((hf.add hg).add (PolynomiallyBounded.const 1)).of_le fun n => Nat.clog_le_of_le_pow ?_
  let e := Nat.clog 2 (f n) + Nat.clog 2 (g n)
  have h₁ : f n ≤ 2 ^ e := (Nat.le_pow_clog (by decide) _).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have h₂ : g n ≤ 2 ^ e := (Nat.le_pow_clog (by decide) _).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  change f n + g n ≤ 2 ^ (e + 1)
  rw [pow_succ, Nat.mul_two]
  exact Nat.add_le_add h₁ h₂

theorem clog_pow (hf : PolynomiallyBounded (fun n => Nat.clog 2 (f n)))
    (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => Nat.clog 2 (f n ^ g n)) := by
  refine (hf.mul hg).of_le fun n => Nat.clog_le_of_le_pow ?_
  change f n ^ g n ≤ 2 ^ (Nat.clog 2 (f n) * g n)
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _

end PolynomiallyBounded

end VPVNP
end Computability
end OAI
