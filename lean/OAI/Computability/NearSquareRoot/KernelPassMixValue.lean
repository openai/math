import OAI.Computability.NearSquareRoot.KernelPass
import OAI.Computability.IntegerMultiplication.Grid.Value

/-! # Common-denominator evaluation of a dyadic mixing row

The row constants determine one binary denominator. Multiplication by their signed
integer numerators and exact addition precede a single fixed-point division.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPassMix

open IntegerMultiplication KernelPass Matrix
open scoped BigOperators

variable {i o A h : ℕ}

/-- Fractional width shared by the whole row, including when the row is empty. -/
def denom (r : Fin i → Coefficient) : ℕ := Finset.univ.sup fun j => (r j).2

/-- Numerator in units of the common denominator. -/
def numerator (D : ℕ) (a : Coefficient) : ℤ := a.1 * 2 ^ (D - a.2)

theorem frac_le_denom (r : Fin i → Coefficient) (j : Fin i) : (r j).2 ≤ denom r :=
  Finset.le_sup (f := fun j => (r j).2) (Finset.mem_univ j)

theorem numerator_eq (D : ℕ) (a : Coefficient) (ha : a.2 ≤ D) :
    (numerator D a : ℚ) = value a * 2 ^ D := by
  unfold numerator value
  push_cast
  conv_rhs => rw [show D = a.2 + (D - a.2) by omega, pow_add]
  field_simp

/-- Exact Gaussian-integer accumulator before the right shift. -/
def accum (r : Fin i → Coefficient) (x : Fin i → Grid.Cell) : Grid.Cell :=
  ∑ j, numerator (denom r) (r j) • x j

/-- Both components of the one-shift evaluation agree with the ideal row sum. -/
theorem toC_accum_div (r : Fin i → Coefficient) (x : Fin i → Grid.Cell) :
    Grid.toC (accum r x) / (2 : ℂ) ^ denom r =
      ∑ j, ((value (r j) : ℚ) : ℂ) * Grid.toC (x j) := by
  have num (j : Fin i) : (numerator (denom r) (r j) : ℂ) =
      (value (r j) : ℂ) * (2 : ℂ)^denom r := by
    exact_mod_cast numerator_eq _ _ (frac_le_denom r j)
  simp only [accum, map_sum, zsmul_eq_mul, map_mul, map_intCast, num, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro j hj
  field_simp

/-- Numerical meaning with input records already on the common fractional grid. -/
theorem accum_meaning (r : Fin i → Coefficient) (p k : ℕ) (x : Fin i → Dusk.Grain k) :
    Grid.toC (accum r (Grid.aspect ∘ x)) / (2:ℂ)^denom r / (2:ℂ)^p =
      ∑ j, (value (r j) : ℂ) * Grid.meaning p k (x j) := by
  rw [toC_accum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Grid.meaning, mul_div_assoc]

/-- The ideal rational matrix at any width is pointwise on the address. -/
theorem mix_mulVec (c : Fin o → Fin i → Coefficient)
    (x : Fin i × Addr A h → ℚ) (b : Fin o) (y : Addr A h) :
    (((Plan.mix (A := A) c).eval h) *ᵥ x) (b,y) =
      ∑ j, value (c b j) * x (j,y) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Plan.eval, ite_mul]

/-- The same addresswise identity after passing to complex fixed-point semantics. -/
theorem mix_complex_mulVec (c : Fin o → Fin i → Coefficient)
    (x : Fin i × Addr A h → ℂ) (b : Fin o) (y : Addr A h) :
    ((((Plan.mix (A := A) c).eval h).map (fun a => (a : ℂ))) *ᵥ x) (b,y) =
      ∑ j, (value (c b j) : ℂ) * x (j,y) := by
  classical
  change (∑ z : Fin i × Addr A h, ((if z.2 = y then value (c b z.1) else 0 : ℚ) : ℂ) * x z) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz]
  · simp

/-- Coefficient growth multiplying a bound on each input component. -/
def rowWeight (r : Fin i → Coefficient) : ℕ :=
  ∑ j, (numerator (denom r) (r j)).natAbs

theorem abs_weighted_sum_le (v : Fin i → ℤ) (B : ℕ) (hv : ∀ j, |v j| ≤ B)
    (r : Fin i → Coefficient) :
    |∑ j, numerator (denom r) (r j) * v j| ≤ (rowWeight r : ℤ) * B := by
  calc
    _ ≤ ∑ j, |numerator (denom r) (r j) * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |numerator (denom r) (r j)| * (B : ℤ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = _ := by
      unfold rowWeight
      push_cast
      rw [Finset.sum_mul]

/-- Headroom for the unshifted accumulator, in magnitude bits. -/
theorem focus_accum (r : Fin i → Coefficient) (x : Fin i → Grid.Cell)
    (B w : ℕ) (hB : ∀ j, |(x j).re| ≤ B ∧ |(x j).im| ≤ B)
    (hw : rowWeight r * B < 2 ^ w) : Grid.focus w (accum r x) := by
  have bound : (rowWeight r : ℤ) * B < 2 ^ w := by exact_mod_cast hw
  have coord (L : Grid.Cell →ₗ[ℤ] ℤ) : L (accum r x) = ∑ j, numerator (denom r) (r j) * L (x j) := by
    simp only [accum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (L.map_smul _ _).trans (zsmul_eq_mul ..)
  constructor
  · change |QuadraticAlgebra.reₗ (-1:ℤ) 0 (accum r x)| < _
    rw [coord]
    exact (abs_weighted_sum_le (fun j => (x j).re) B (fun j => (hB j).1) r).trans_lt bound
  · change |QuadraticAlgebra.imₗ (-1:ℤ) 0 (accum r x)| < _
    rw [coord]
    exact (abs_weighted_sum_le (fun j => (x j).im) B (fun j => (hB j).2) r).trans_lt bound

/-- The temporary accumulator needs only this constant number of extra magnitude bits
for the fixed coefficient row, independently of the input width. -/
def guardBits (r : Fin i → Coefficient) : ℕ := Nat.clog 2 (rowWeight r + 1)

/-- Every partial sum in the integer accumulation fits at the guarded width.
This includes the individual scaled terms and the complete accumulator. -/
theorem partial_accum_fits (r : Fin i → Coefficient) (k : ℕ)
    (x : Fin i → Dusk.Grain k) (s : Finset (Fin i)) :
    Grid.focus (k + guardBits r) (∑ j ∈ s, numerator (denom r) (r j) • Grid.aspect (x j)) := by
  let z (j : Fin i) := if j ∈ s then Grid.aspect (x j) else 0
  have hz (j : Fin i) : |(z j).re| ≤ (2^k : ℕ) ∧ |(z j).im| ≤ (2^k : ℕ) := by
    by_cases hj : j ∈ s
    · simpa only [z, hj, ite_true, Nat.cast_pow, Nat.cast_ofNat] using
        And.intro (Grid.aspect_f (x j)).1.le (Grid.aspect_f (x j)).2.le
    · simp [z, hj]
  have hg : rowWeight r < 2^guardBits r := Nat.le_pow_clog (by decide) (rowWeight r + 1)
  have hpow : rowWeight r * 2^k < 2^(k + guardBits r) := by
    rw [pow_add, Nat.mul_comm (2^k)]
    exact Nat.mul_lt_mul_of_pos_right hg (by positivity)
  convert focus_accum r z _ _ hz hpow using 1
  unfold accum z
  simp only [Finset.sum_ite_mem, Finset.univ_inter, smul_ite, smul_zero]

/-- Exact unrounded accumulator interpretation against the DSL matrix itself. -/
theorem accum_eq_mix (c : Fin o → Fin i → Coefficient) (p k : ℕ)
    (x : Fin i × Addr A h → Dusk.Grain k) (b : Fin o) (y : Addr A h) :
    Grid.toC (accum (c b) (fun j => Grid.aspect (x (j,y)))) / (2:ℂ)^denom (c b) / (2:ℂ)^p =
    ((((Plan.mix (A := A) c).eval h).map (fun a => (a : ℂ))) *ᵥ
      fun z => Grid.meaning p k (x z)) (b,y) := by
  rw [mix_complex_mulVec]
  exact accum_meaning (c b) p k (fun j => x (j,y))

end KernelPassMix

end NearSquareRoot
end Computability
end OAI
