import OAI.LinearAlgebra.FiniteFourier.RingTernaryWord
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # The three-cycle and its inverse as ternary Fourier words

With the forward cycle sending coordinate zero to coordinate one, Fourier
transformation diagonalizes `I + aP` with eigenvalues `1+a`, `1+aζ` and
`1+aζ²`. Each is a unit whenever their product `1+a³` is a unit. Both
matrix words use two forward Fourier slots and two unit monomial slots.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R]

/-- The identity plus `a` times the forward three-cycle. -/
def ternaryCycleSum (a : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, a; a, 1, 0; 0, a, 1]

/-- The signed adjugate formula, where `t` is the inverse of `1+a³`. -/
def ternaryCycleInv (a t : R) : Matrix (Fin 3) (Fin 3) R :=
  !![t, a^2*t, -a*t; -a*t, t, a^2*t; a^2*t, -a*t, t]

theorem ternaryCycleSum_mul_inv (a t : R) (ht : (1+a^3)*t=1) :
    ternaryCycleSum a * ternaryCycleInv a t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ternaryCycleSum, ternaryCycleInv, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply] <;> first | ring1 | linear_combination ht

private theorem fourier_explicit (ζ : R) (hζ : ζ^2+ζ+1=0) :
    ringTernaryDFT ζ = !![1, 1, 1; 1, ζ, ζ^2; 1, ζ^2, ζ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [ringTernaryDFT]
  linear_combination (ζ^2-ζ)*hζ

private def eigenvalues (ζ a : R) : Fin 3 → R := ![1+a, 1+a*ζ, 1+a*ζ^2]

private theorem fourier_intertwines (ζ a : R) (hζ : ζ^2+ζ+1=0) :
    ringTernaryDFT ζ * ternaryCycleSum a = diagonal (eigenvalues ζ a) * ringTernaryDFT ζ := by
  rw [fourier_explicit ζ hζ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ternaryCycleSum, eigenvalues, Matrix.diagonal_mul, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    first | ring1 | linear_combination -a*(ζ-1)*hζ | linear_combination -a*ζ*(ζ-1)*hζ

private theorem eigenvalues_units (ζ a : R) (hζ : ζ^2+ζ+1=0) (ha : IsUnit (1+a^3)) :
    ∀ i, IsUnit (eigenvalues ζ a i) := by
  have hprod : ((1+a)*(1+a*ζ))*(1+a*ζ^2)=1+a^3 := by
    linear_combination (a+a^2*ζ+a^3*(ζ-1))*hζ
  rw [← hprod] at ha
  obtain ⟨h01,h2⟩ := IsUnit.mul_iff.mp ha
  obtain ⟨h0,h1⟩ := IsUnit.mul_iff.mp h01
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Reversing the frequency indices and multiplying by the inverse of three
turns a forward ternary transform into its inverse. -/
private def reverseScale (t : R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => if Equiv.swap (1 : Fin 3) 2 i = j then t else 0

private theorem reverseScale_fourier_inv (ζ t : R) (hζ : ζ^2+ζ+1=0) (ht : 3*t=1) :
    (reverseScale t * ringTernaryDFT ζ) * ringTernaryDFT ζ = 1 := by
  rw [fourier_explicit ζ hζ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reverseScale, Equiv.swap_apply_def, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply] <;>
    first | linear_combination ht | linear_combination t*hζ |
      linear_combination ht + 2*t*(ζ-1)*hζ | linear_combination t*(ζ^2-ζ+1)*hζ

private theorem reverseScale_word (ζ : R) (t : Rˣ) :
    RingTernaryWord ζ 1 (reverseScale (t : R)) :=
  .monomial (Equiv.swap 1 2) (fun _ => t)

/-- The four-slot Fourier word for the forward cycle sum. -/
theorem ringTernaryWord_cycleSum (ζ a : R) (hζ : ζ^2+ζ+1=0) (h3 : IsUnit (3:R))
    (ha : IsUnit (1+a^3)) : RingTernaryWord ζ 4 (ternaryCycleSum a) := by
  let t := h3.unit⁻¹
  have ht : 3*(t:R)=1 := h3.unit.mul_inv
  let u := fun i => (eigenvalues_units ζ a hζ ha i).unit
  have hu : (fun i => (u i : R)) = eigenvalues ζ a := funext fun _ => IsUnit.unit_spec _
  have hD := reverseScale_fourier_inv ζ t hζ ht
  have hm := (reverseScale_word ζ t).mul (.fourier (ζ := ζ))
  have hw := hm.mul ((RingTernaryWord.diagonal (ζ := ζ) u).mul .fourier)
  rw [hu, ← fourier_intertwines ζ a hζ, ← Matrix.mul_assoc, hD, one_mul] at hw
  exact hw

/-- Inverting the three diagonal eigenvalues gives the four-slot word for the
signed inverse, still using only forward ternary kernels. -/
theorem ringTernaryWord_cycleInv (ζ a t : R) (hζ : ζ^2+ζ+1=0) (h3 : IsUnit (3:R))
    (ht : (1+a^3)*t=1) : RingTernaryWord ζ 4 (ternaryCycleInv a t) := by
  let s := h3.unit⁻¹
  have hs : 3*(s:R)=1 := h3.unit.mul_inv
  have ha : IsUnit (1+a^3) := isUnit_iff_exists_inv.mpr ⟨t, ht⟩
  let u := fun i => (eigenvalues_units ζ a hζ ha i).unit
  let E := diagonal (fun i => ((u i)⁻¹ : Rˣ).val)
  have hu : E * diagonal (eigenvalues ζ a) = 1 := by
    rw [show eigenvalues ζ a = fun i => (u i : R) from funext fun _ => (IsUnit.unit_spec _).symm]
    simp [E, diagonal_mul_diagonal]
  have hEF : (E * ringTernaryDFT ζ) * ternaryCycleSum a = ringTernaryDFT ζ := by
    rw [Matrix.mul_assoc, fourier_intertwines ζ a hζ, ← Matrix.mul_assoc, hu, one_mul]
  have hEF' : E * ringTernaryDFT ζ = ringTernaryDFT ζ * ternaryCycleInv a t := by
    calc
      _ = (E * ringTernaryDFT ζ) * (ternaryCycleSum a * ternaryCycleInv a t) := by
        rw [ternaryCycleSum_mul_inv a t ht, mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hEF]
  have hD := reverseScale_fourier_inv ζ s hζ hs
  have hm := (reverseScale_word ζ s).mul (.fourier (ζ := ζ))
  have hw := hm.mul ((RingTernaryWord.diagonal (ζ := ζ) fun i => (u i)⁻¹).mul .fourier)
  change RingTernaryWord ζ 4 ((reverseScale (s:R) * ringTernaryDFT ζ) * (E * ringTernaryDFT ζ)) at hw
  rw [hEF', ← Matrix.mul_assoc, hD, one_mul] at hw
  exact hw

end FiniteFourier
end LinearAlgebra
end OAI
