import OAI.Computability.VPVNP.EvaluatorChronologicalLoop
import OAI.Computability.VPVNP.EvaluatorDigitAction

/-!
# Time allowance for native radix conversion and the chronological scheduler

The clock includes the initial reversal of the RAM's exponent array, the
restoring divisions that prepare all digit rows, and the two nested tally
loops. For fixed field, label count and callback allowances it is quadratic
in the input exponent width. Polynomial growth of the callback allowances in
that width is also permitted.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorScheduleBudget

open EvaluatorRadixRows EvaluatorRadixDivision EvaluatorDigitAction EvaluatorChronologicalLoop

/-- Exact deterministic preparation time followed by the scheduler's reserved
clock. The two callback allowances cover one label and one Frobenius query. -/
def scheduleBudget (t Z ℓ Q B BF : ℕ) :=
  2*(t*Z)+1+rowsTicks t Z ℓ + traverseBudget t Z BF (cellBudget t Z ℓ Q B)

private def quadratic (t ℓ : ℕ) := t*(10*ℓ+10) + t^2*(19+13*ℓ)
private def linear (t ℓ Q : ℕ) := t*(9*ℓ+31) + 7 + t*Q*(4*ℓ+3)
private def constant (t : ℕ) := 5*t+4

private theorem expand (t Z ℓ Q B BF : ℕ) :
    scheduleBudget t Z ℓ Q B BF = quadratic t ℓ * Z^2 +
      (linear t ℓ Q + t*Q*B + BF) * Z + constant t := by
  unfold scheduleBudget rowsTicks rowTicks radixTicks digitTicks traverseBudget columnBudget
    cellBudget quadratic linear constant
  ring

/-- A polynomial multiplier independent of the exponent width. -/
def coefficient (t ℓ Q B BF : ℕ) :=
  t*(10*ℓ+10) + t^2*(19+13*ℓ) + (t*(9*ℓ+31) + 7 + t*Q*(4*ℓ+3) + t*Q*B + BF) + (5*t+4)

/-- Uniform in the exponent words and the chosen sequence of matrix indices. -/
theorem scheduleBudget_le (t Z ℓ Q B BF : ℕ) :
    scheduleBudget t Z ℓ Q B BF ≤ coefficient t ℓ Q B BF * (Z+1)^2 := by
  have h₂ : Z^2 ≤ (Z+1)^2 := Nat.pow_le_pow_left (Nat.le_succ _) _
  have h₁ : Z ≤ (Z+1)^2 := by rw [pow_two]; nlinarith
  have h₀ : 1 ≤ (Z+1)^2 := Nat.pow_pos (Nat.succ_pos Z)
  rw [expand]
  calc
    _ ≤ quadratic t ℓ * (Z+1)^2 + (linear t ℓ Q + t*Q*B + BF) * (Z+1)^2 +
        constant t * (Z+1)^2 :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h₂) (Nat.mul_le_mul_left _ h₁))
        (by simpa using Nat.mul_le_mul_left (constant t) h₀)
    _ = _ := by simp only [coefficient, quadratic, linear, constant]; ring

private theorem coefficient_le {t ℓ Q B BF E D : ℕ} (hE : 1 ≤ E) (hD : 1 ≤ D)
    (ht : t ≤ E) (hℓ : ℓ ≤ E) (hQ : Q ≤ E) (hB : B ≤ E*D) (hF : BF ≤ E*D) :
    coefficient t ℓ Q B BF ≤ 128*E^3*D := by
  have hmono : coefficient t ℓ Q B BF ≤ coefficient E E E (E*D) (E*D) := by
    unfold coefficient; gcongr
  have hscale : coefficient E E E (E*D) (E*D) ≤ coefficient E E E E E * D := by
    let fixed := quadratic E E + linear E E E + constant E
    calc
      _ = fixed + (E^3+E)*D := by dsimp [fixed, quadratic, linear, constant, coefficient]; ring
      _ ≤ fixed*D + (E^3+E)*D := Nat.add_le_add_right (by simpa using Nat.mul_le_mul_left fixed hD) _
      _ = coefficient E E E E E * D := by dsimp [fixed, quadratic, linear, constant, coefficient]; ring
  have h₁ : E ≤ E^2 := by simpa [pow_two] using Nat.mul_le_mul_left E hE
  have h₂ : E^2 ≤ E^3 := by simpa only [pow_succ E 2, Nat.mul_one] using Nat.mul_le_mul_left (E^2) hE
  have hbase : coefficient E E E E E ≤ 128*E^3 := by
    rw [show coefficient E E E E E = 18*E^3+41*E^2+47*E+11 by unfold coefficient; ring]
    omega
  exact hmono.trans (hscale.trans (Nat.mul_le_mul_right D hbase))

/-- When all fixed parameters are at most `2^a` and callbacks take at most
`2^a * (Z+1)^k`, the coefficient stays singly exponential in `a` and the
degree in `Z` grows by at most two. The same `a` and `k` may be used across
any collection of fields, dimensions or advice parameters with those bounds. -/
theorem scheduleBudget_le_exp_poly (t Z ℓ Q B BF a k : ℕ)
    (ht : t ≤ 2^a) (hℓ : ℓ ≤ 2^a) (hQ : Q ≤ 2^a)
    (hB : B ≤ 2^a*(Z+1)^k) (hF : BF ≤ 2^a*(Z+1)^k) :
    scheduleBudget t Z ℓ Q B BF ≤ 2^(3*a+7)*(Z+1)^(k+2) := by
  have hc := coefficient_le (Nat.pow_pos (by decide)) (Nat.pow_pos (Nat.succ_pos Z)) ht hℓ hQ hB hF
  calc
    _ ≤ (128*(2^a)^3*(Z+1)^k)*(Z+1)^2 :=
      (scheduleBudget_le ..).trans (Nat.mul_le_mul_right _ hc)
    _ = _ := by rw [Nat.mul_comm 3 a, pow_add, pow_mul, pow_add]; ring

end EvaluatorScheduleBudget

end VPVNP
end Computability
end OAI
