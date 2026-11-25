import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.Tactic.LinearCombination

/-! # Unit pivots in the ternary shear compiler

The matrices attached to the three-cycle use the parameters `a` and `a²`.
Their determinants and the difference of their cubed parameters are invertible
when `a` is a ninth root of unity of exact order nine in every residue field.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R] {a ω : R}

/-- The cubic cyclotomic relation gives a cube root of unity in any ring. -/
theorem ternaryOmega_pow_three (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

/-- The Fourier phase and its difference from one are units when three is invertible. -/
theorem ternaryOmegaUnits (hω : ω ^ 2 + ω + 1 = 0) (h₃ : IsUnit (3 : R)) :
    IsUnit ω ∧ IsUnit (ω - 1) := by
  refine ⟨(isUnit_pow_iff (by decide : 3 ≠ 0)).mp ?_, isUnit_of_dvd_unit ?_ h₃⟩
  · rw [ternaryOmega_pow_three hω]
    exact isUnit_one
  · exact ⟨-(ω + 2), by linear_combination hω⟩

/-- Invertibility of the ninth-root parameters follows from a single unit difference. -/
theorem ternaryCycleUnits_of_cube_sub_one (ha : a ^ 9 = 1) (hsub : IsUnit (a ^ 3 - 1)) :
    IsUnit a ∧ IsUnit (a ^ 3 - 1) ∧ IsUnit (a ^ 6 - a ^ 3) ∧
      IsUnit (1 + a ^ 3) ∧ IsUnit (1 + a ^ 6) := by
  have hu : IsUnit a := (isUnit_pow_iff (by decide : 9 ≠ 0)).mp (ha ▸ isUnit_one)
  have hs : 1 + a ^ 3 + a ^ 6 = 0 := by
    apply hsub.mul_left_cancel
    linear_combination ha
  have hd : a ^ 6 - a ^ 3 = a ^ 3 * (a ^ 3 - 1) := by ring
  have h₁ : 1 + a ^ 3 = -(a ^ 6) := by linear_combination hs
  have h₂ : 1 + a ^ 6 = -(a ^ 3) := by linear_combination hs
  exact ⟨hu, hsub, hd ▸ (hu.pow 3).mul hsub, h₁ ▸ (hu.pow 6).neg, h₂ ▸ (hu.pow 3).neg⟩

/-- A ninth root of exact order nine in every residue field supplies all the unit
pivots of the three-cycle construction. -/
theorem ternaryCycleUnits (ha : a ^ 9 = 1)
    (hres : ∀ m : MaximalSpectrum R, IsPrimitiveRoot (Ideal.Quotient.mk m.asIdeal a) 9) :
    IsUnit a ∧ IsUnit (a ^ 3 - 1) ∧ IsUnit (a ^ 6 - a ^ 3) ∧
      IsUnit (1 + a ^ 3) ∧ IsUnit (1 + a ^ 6) := by
  apply ternaryCycleUnits_of_cube_sub_one ha
  by_contra hn
  obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hn)
  have he : Ideal.Quotient.mk I (a ^ 3 - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_sub, map_pow, map_one, sub_eq_zero] at he
  exact (hres ⟨I, hI⟩).pow_ne_one_of_pos_of_lt (by decide : 3 ≠ 0) (by decide) he

end FiniteFourier
end LinearAlgebra
end OAI
