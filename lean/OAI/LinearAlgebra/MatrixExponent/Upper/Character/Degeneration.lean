import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Powers
import OAI.LinearAlgebra.MatrixExponent.Upper.SeparationInterpolation
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# Characters and polynomial degenerations

Restriction monotonicity suffices for a polynomial degeneration.  For each
fixed family, interpolation of its tensor powers costs only linearly many
copies.  The elementary estimate below removes that overhead without any
assumed continuity of the character.
-/

noncomputable section

open scoped NNReal
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper

/-- A fixed linear overhead cannot mask a strictly larger exponential rate.
The proof uses Bernoulli's inequality twice, rather than a limit theorem. -/
theorem le_of_pow_le_linear_mul_pow (a b K : ℝ)
    (ha : 0 ≤ a) (_hb : 0 ≤ b) (_hK : 0 ≤ K)
    (h : ∀ n : ℕ, b ^ n ≤ (K * (n : ℝ) + 1) * a ^ n) : b ≤ a := by
  by_contra hba
  have hab : a < b := lt_of_not_ge hba
  have ha' : 0 < a := by
    by_contra hapos
    have haz : a = 0 := le_antisymm (le_of_not_gt hapos) ha
    have hh := h 1
    simp only [pow_one, Nat.cast_one, mul_one, haz, mul_zero] at hh
    linarith
  let r := b / a
  have hr : 1 < r := (lt_div_iff₀ ha').mpr (by simpa using hab)
  have hrpow : ∀ n : ℕ, r ^ n ≤ K * (n : ℝ) + 1 := by
    intro n
    dsimp [r]
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos ha' n)).mpr (h n)
  have hdelta : 0 < (r - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr)
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((2 * K + 1) / (r - 1) ^ 2))
  have hn1 : (1 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hngap : 2 * K + 1 < (n : ℝ) * (r - 1) ^ 2 :=
    (div_lt_iff₀ hdelta).mp (lt_of_le_of_lt (le_max_right _ _) hn)
  have hbern := one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ r) n
  have hsmall : 0 ≤ (n : ℝ) * (r - 1) := mul_nonneg hn0.le (sub_pos.mpr hr).le
  have hsq : ((n : ℝ) * (r - 1)) ^ 2 ≤ (r ^ n) ^ 2 := by
    have hrn : 0 ≤ r ^ n := pow_nonneg (by linarith) n
    nlinarith
  have hupper := hrpow (n * 2)
  rw [pow_mul] at hupper
  push_cast at hupper
  have hstrict := mul_lt_mul_of_pos_left hngap hn0
  nlinarith

namespace TensorClass

/-- Every normalized restriction-monotone character is monotone on the
constant coefficient of an actual bounded polynomial restriction family.
The degree is fixed before the tensor-power argument is applied. -/
theorem Character.polynomial_constant_le (f : Character)
    {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor Coeff X Y Z) (D : Tensor Coeff U V W)
    (P : Tensor (Polynomial Coeff) U V W) (K : ℕ)
    (hconstant : ∀ u v w, (P u v w).coeff 0 = D u v w)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (heval : ∀ t : Coeff, t ≠ 0 →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T) :
    f (ofTensor D) ≤ f (ofTensor T) := by
  have hpower : ∀ j : ℕ,
      (f (ofTensor D)) ^ j ≤ (K * j + 1 : ℝ≥0) * (f (ofTensor T)) ^ j := by
    intro j
    have hr := Separation.polynomial_power_mem_restrictionOrbit
      T D P K hconstant hdegree heval j
    have hmono := f.monotone' (ofTensor_le hr)
    simpa only [Character.map_directSum_const, Character.map_power_tensor,
      Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hmono
  have hreal := le_of_pow_le_linear_mul_pow
    (f (ofTensor T) : ℝ) (f (ofTensor D) : ℝ) (K : ℝ)
    (f (ofTensor T)).coe_nonneg (f (ofTensor D)).coe_nonneg (Nat.cast_nonneg K)
    (fun j => by exact_mod_cast hpower j)
  exact_mod_cast hreal

end TensorClass
end OAI.LinearAlgebra.MatrixExponent.Upper
