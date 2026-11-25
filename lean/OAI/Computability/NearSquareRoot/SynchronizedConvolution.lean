import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exact normalized transform of the occupied residue box

The frequency kernel is a product of the positive-sign standard characters of its cyclic
axes. Two normalized forward transforms, a pointwise product, the adjoint, and the final
square-root factor recover cyclic convolution in the product group.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ResidueFourier

noncomputable section
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} [∀ i, NeZero (a i)]

/-- The group of valid addresses, before extending each cyclic axis by an identity block. -/
abbrev Box (a : ι → ℕ) := (i : ι) → ZMod (a i)

/-- The unscaled positive-sign Fourier kernel. -/
def phase (x y : Box a) : ℂ := ∏ i, ZMod.stdAddChar (x i * y i)

omit [DecidableEq ι] in
private theorem phase_add_left (x y z : Box a) : phase (x + y) z = phase x z * phase y z := by
  simp [phase, add_mul, AddChar.map_add_eq_mul, prod_mul_distrib]

theorem phase_orthogonality (x : Box a) :
    ∑ y, phase x y = if x = 0 then (Fintype.card (Box a) : ℂ) else 0 := by
  classical
  have axis (i : ι) : ∑ t : ZMod (a i), ZMod.stdAddChar (x i * t) =
      if x i = 0 then (a i : ℂ) else 0 := by
    split_ifs with h
    · simp [h]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar _ h)
  unfold phase
  rw [← Fintype.prod_sum (fun i (t : ZMod (a i)) => ZMod.stdAddChar (x i * t))]
  simp_rw [axis]
  split_ifs with h
  · subst x
    simp [Box, Fintype.card_pi]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! hn
      exact h (funext hn)
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

/-- Square root of the number of valid addresses. -/
def scale (a : ι → ℕ) [∀ i, NeZero (a i)] : ℂ := (Real.sqrt (Fintype.card (Box a)) : ℝ)

theorem scale_sq : (scale a)^2 = (Fintype.card (Box a) : ℂ) := by
  unfold scale
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (Box a)) : (0 : ℝ) ≤ _)

theorem scale_ne_zero : scale a ≠ 0 := by
  unfold scale
  exact_mod_cast Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr Fintype.card_pos)

/-- Unscaled positive-sign Fourier transform on all valid axes at once. -/
def transform (f : Box a → ℂ) (k : Box a) : ℂ := ∑ x, phase x k * f x

/-- Normalized Fourier transform. -/
def forward (f : Box a → ℂ) (k : Box a) : ℂ := (scale a)⁻¹ * transform f k

/-- The adjoint transform has the negative sign and the same normalization. -/
def adjoint (f : Box a → ℂ) (x : Box a) : ℂ := (scale a)⁻¹ * ∑ k, phase (-x) k * f k

/-- Cyclic convolution in residue coordinates. -/
def convolution {G : Type*} [Fintype G] [AddGroup G] (f g : G → ℂ) (x : G) : ℂ :=
  ∑ y, f y * g (x - y)

/-- A CRT additive isomorphism transports cyclic convolution in both directions. -/
theorem convolution_reindex {G H : Type*} [Fintype G] [Fintype H] [AddGroup G] [AddGroup H]
    (e : G ≃+ H) (f g : H → ℂ) (x : G) :
    convolution (f ∘ e) (g ∘ e) x = convolution f g (e x) := by
  unfold convolution
  exact Fintype.sum_equiv e.toEquiv _ _ fun y => by simp

/-- Character multiplication converts a cyclic convolution to coordinatewise multiplication. -/
theorem transform_convolution (f g : Box a → ℂ) (k : Box a) :
    transform (convolution f g) k = transform f k * transform g k := by
  unfold transform convolution
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun z => by
    simp only [Equiv.subRight_apply]
    rw [show phase z k = phase y k * phase (z-y) k by
      rw [← phase_add_left]; congr 1; abel]
    ring

theorem inverse_sum (f : Box a → ℂ) (x : Box a) :
    ∑ k, phase (-x) k * transform f k = (Fintype.card (Box a) : ℂ) * f x := by
  unfold transform
  simp_rw [mul_sum, ← mul_assoc, ← phase_add_left]
  rw [sum_comm]
  simp_rw [← sum_mul, phase_orthogonality]
  simp [neg_add_eq_zero, ite_mul]

/-- The unitary convolution algorithm in `integers.tex`, including its final scaling. -/
theorem recover_convolution (f g : Box a → ℂ) (x : Box a) :
    scale a * adjoint (fun k => forward f k * forward g k) x = convolution f g x := by
  have h (k : Box a) : phase (-x) k * (forward f k * forward g k) =
      ((scale a)^2)⁻¹ * (phase (-x) k * transform (convolution f g) k) := by
    rw [transform_convolution]
    simp only [forward, pow_two, mul_inv_rev]
    ring
  unfold adjoint
  simp_rw [h]
  rw [← mul_sum, inverse_sum, ← scale_sq]
  field_simp [scale_ne_zero]

end
end ResidueFourier

end NearSquareRoot
end Computability
end OAI
