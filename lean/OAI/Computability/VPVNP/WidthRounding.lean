import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer wire widths in the shrinking step

Section 7.2 of *VP and VNP differ over every field* divides a bundled wire
into equal-mass slots. An integral width `b` splits into slots of widths
`b / q` and `b / q + 1`. The excess in the sum of squares is exactly
`r * (q - r) / q`, where `r` is the remainder, and hence is at most `q / 4`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open scoped BigOperators

/-- The first `b % q` slots receive the extra bit. -/
def splitWidth (b q : ℕ) (i : Fin q) : ℕ :=
  if i.val < b % q then b / q + 1 else b / q

private theorem sum_splitWidth_apply {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (b q : ℕ) (hq : 0 < q) :
    ∑ i : Fin q, f (splitWidth b q i) =
      (b % q) • f (b / q + 1) + (q - b % q) • f (b / q) := by
  let r : Fin q := ⟨b % q, Nat.mod_lt _ hq⟩
  have hlo : Finset.univ.filter (fun i : Fin q => i < r) = Finset.Iio r := by ext; simp
  have hhi : Finset.univ.filter (fun i : Fin q => ¬ i < r) = Finset.Ici r := by ext; simp
  change (∑ i : Fin q, f (if i < r then b / q + 1 else b / q)) = _
  simp only [apply_ite f, Finset.sum_ite, hlo, hhi, Finset.sum_const, Fin.card_Iio, Fin.card_Ici, r]

/-- Concatenating the split payloads recovers exactly the old bit count. -/
theorem sum_splitWidth (b q : ℕ) (hq : 0 < q) : ∑ i : Fin q, splitWidth b q i = b := by
  have hr := Nat.mod_lt b hq
  calc
    ∑ i : Fin q, splitWidth b q i =
        b % q * (b / q + 1) + (q - b % q) * (b / q) := by
      simpa using sum_splitWidth_apply id b q hq
    _ = (b % q + (q - b % q)) * (b / q) + b % q := by ring
    _ = b := by rw [show b % q + (q - b % q) = q by omega, Nat.div_add_mod]

/-- Exact sum of squared widths, expressed as the fractional optimum plus the
rounding error. -/
theorem sum_splitWidth_sq (b q : ℕ) (hq : 0 < q) :
    ∑ i : Fin q, (splitWidth b q i : ℝ) ^ 2 =
      (b : ℝ) ^ 2 / q + (b % q : ℕ) * ((q : ℝ) - (b % q : ℕ)) / q := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hb : (b : ℝ) = (q : ℝ) * (b / q : ℕ) + (b % q : ℕ) := by
    exact_mod_cast (Nat.div_add_mod b q).symm
  rw [sum_splitWidth_apply (fun w : ℕ => (w : ℝ) ^ 2) b q hq, hb]
  simp only [nsmul_eq_mul, Nat.cast_sub (Nat.mod_lt _ hq).le, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The error from rounding all the widths is at most one quarter per slot. -/
theorem sum_splitWidth_sq_le (b q : ℕ) (hq : 0 < q) :
    ∑ i : Fin q, (splitWidth b q i : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 / q + q / 4 := by
  rw [sum_splitWidth_sq _ _ hq]
  apply add_le_add_right
  apply (div_le_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
  nlinarith [sq_nonneg ((q : ℝ) / 2 - (b % q : ℕ))]

/-- With mass `p` per slot, the energy penalty for integral splitting is at
most `q / (4*p)`. This applies to both subdivisions in Section 7.2. -/
theorem splitWidth_energy_le (b q : ℕ) (hq : 0 < q) (p : ℝ) (hp : 0 < p) :
    ∑ i : Fin q, (splitWidth b q i : ℝ) ^ 2 / p ≤ (b : ℝ) ^ 2 / (q * p) + q / (4 * p) := by
  rw [← Finset.sum_div]
  calc
    _ ≤ ((b : ℝ) ^ 2 / q + q / 4) / p :=
      div_le_div_of_nonneg_right (sum_splitWidth_sq_le _ _ hq) hp.le
    _ = _ := by rw [add_div, div_div, div_div]

end Compression

end VPVNP
end Computability
end OAI
