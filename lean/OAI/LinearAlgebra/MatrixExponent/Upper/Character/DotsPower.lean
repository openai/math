import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.Dots
import OAI.LinearAlgebra.TensorSpectrum.CharacterPower

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# Character exponents of the auxiliary pairings

The power laws follow from the actual coordinate restrictions and product
identities. Their exponents are constructed here, rather than supplied as
assumptions about a character.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass.Character

theorem exists_dotX_power (f : Character) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n → f.dotXValue n = (n : ℝ) ^ p := by
  apply TensorSpectrum.exists_power_of_monotone_multiplicative f.dotXValue
  · intro m n hm hn
    exact f.dotXValue_mul m n
  · intro m n hm hmn
    exact f.dotXValue_mono hmn
  · intro n hn
    exact ⟨f.one_le_dotXValue (Nat.lt_of_lt_of_le Nat.zero_lt_one hn),
      f.dotXValue_le n⟩

theorem exists_dotY_power (f : Character) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n → f.dotYValue n = (n : ℝ) ^ p := by
  apply TensorSpectrum.exists_power_of_monotone_multiplicative f.dotYValue
  · intro m n hm hn
    exact f.dotYValue_mul m n
  · intro m n hm hmn
    exact f.dotYValue_mono hmn
  · intro n hn
    exact ⟨f.one_le_dotYValue (Nat.lt_of_lt_of_le Nat.zero_lt_one hn),
      f.dotYValue_le n⟩

theorem exists_dotZ_power (f : Character) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n → f.dotZValue n = (n : ℝ) ^ p := by
  apply TensorSpectrum.exists_power_of_monotone_multiplicative f.dotZValue
  · intro m n hm hn
    exact f.dotZValue_mul m n
  · intro m n hm hmn
    exact f.dotZValue_mono hmn
  · intro n hn
    exact ⟨f.one_le_dotZValue (Nat.lt_of_lt_of_le Nat.zero_lt_one hn),
      f.dotZValue_le n⟩

noncomputable def pX (f : Character) : ℝ := Classical.choose f.exists_dotX_power
noncomputable def pY (f : Character) : ℝ := Classical.choose f.exists_dotY_power
noncomputable def pZ (f : Character) : ℝ := Classical.choose f.exists_dotZ_power

theorem pX_nonneg (f : Character) : 0 ≤ f.pX :=
  (Classical.choose_spec f.exists_dotX_power).1

theorem pY_nonneg (f : Character) : 0 ≤ f.pY :=
  (Classical.choose_spec f.exists_dotY_power).1

theorem pZ_nonneg (f : Character) : 0 ≤ f.pZ :=
  (Classical.choose_spec f.exists_dotZ_power).1

theorem pX_le_one (f : Character) : f.pX ≤ 1 :=
  (Classical.choose_spec f.exists_dotX_power).2.1

theorem pY_le_one (f : Character) : f.pY ≤ 1 :=
  (Classical.choose_spec f.exists_dotY_power).2.1

theorem pZ_le_one (f : Character) : f.pZ ≤ 1 :=
  (Classical.choose_spec f.exists_dotZ_power).2.1

theorem dotXValue_eq_rpow (f : Character) (n : ℕ) (hn : 1 ≤ n) :
    f.dotXValue n = (n : ℝ) ^ f.pX :=
  (Classical.choose_spec f.exists_dotX_power).2.2 n hn

theorem dotYValue_eq_rpow (f : Character) (n : ℕ) (hn : 1 ≤ n) :
    f.dotYValue n = (n : ℝ) ^ f.pY :=
  (Classical.choose_spec f.exists_dotY_power).2.2 n hn

theorem dotZValue_eq_rpow (f : Character) (n : ℕ) (hn : 1 ≤ n) :
    f.dotZValue n = (n : ℝ) ^ f.pZ :=
  (Classical.choose_spec f.exists_dotZ_power).2.2 n hn

theorem square_value_eq_rpow (f : Character) (n : ℕ) (hn : 1 ≤ n) :
    (f (square n) : ℝ) = (n : ℝ) ^ (f.pX + f.pY + f.pZ) := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [← f.dotValues_product n, f.dotXValue_eq_rpow n hn,
    f.dotYValue_eq_rpow n hn, f.dotZValue_eq_rpow n hn,
    ← Real.rpow_add hnR, ← Real.rpow_add hnR]

theorem sum_exponents_nonneg (f : Character) : 0 ≤ f.pX + f.pY + f.pZ :=
  add_nonneg (add_nonneg f.pX_nonneg f.pY_nonneg) f.pZ_nonneg

theorem sum_exponents_le_three (f : Character) : f.pX + f.pY + f.pZ ≤ 3 := by
  have hx := f.pX_le_one
  have hy := f.pY_le_one
  have hz := f.pZ_le_one
  linarith

end OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass.Character
