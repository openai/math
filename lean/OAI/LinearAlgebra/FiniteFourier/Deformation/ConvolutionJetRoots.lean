import Mathlib.Dynamics.Newton
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Root lifting at the two deformation endpoints

The simple-root step works over any commutative ring with a nilpotent parameter.
The congruences below are modulo the parameter itself, even if the coefficient ring
has other nilpotents. We apply the step at the split endpoint and at the original
quadratic and binomial generators.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial

variable {R : Type*} [CommRing R]

private theorem nilpotent_of_parameter_dvd {z x : R} (hz : IsNilpotent z) (hx : z ∣ x) :
    IsNilpotent x := by
  obtain ⟨k, rfl⟩ := hx
  exact (Commute.all _ _).isNilpotent_mul_right hz

/-- The coordinate of a finite jet is nilpotent. This also covers its image in every
algebra over the jet ring by mapping the nilpotence identity. -/
theorem jetParameter_nilpotent (R : Type*) [CommRing R] (h : ℕ) :
    IsNilpotent (AdjoinRoot.root ((X : R[X]) ^ h)) := by
  exact ⟨h, by simpa using AdjoinRoot.eval₂_root ((X : R[X]) ^ h)⟩

/-- Lift a simple root uniquely through a nilpotent principal ideal. -/
theorem existsUnique_root_congr {z x : R} (hz : IsNilpotent z) (p : R[X])
    (hx : z ∣ p.eval x) (hd : IsUnit (p.derivative.eval x)) :
    ∃! y : R, z ∣ y - x ∧ p.eval y = 0 := by
  have hnil := nilpotent_of_parameter_dvd hz hx
  obtain ⟨y, ⟨hy, hroot⟩, unique⟩ :=
    p.existsUnique_nilpotent_sub_and_aeval_eq_zero (x := x)
      (by simpa only [coe_aeval_eq_eval] using hnil)
      (by simpa only [coe_aeval_eq_eval] using hd)
  change p.eval y = 0 at hroot
  have hy' : IsNilpotent (y - x) := by simpa using hy.neg
  obtain ⟨c, hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add p x (y - x)
  rw [add_sub_cancel, hroot] at hc
  have hu : IsUnit (p.derivative.eval x + c * (y - x)) :=
    ((Commute.all _ _).isNilpotent_mul_left hy').isUnit_add_left_of_commute hd (.all _ _)
  have hfac : (p.derivative.eval x + c * (y - x)) * (y - x) = -p.eval x := by
    linear_combination hc
  refine ⟨y, ⟨hu.dvd_mul_left.mp (hfac ▸ dvd_neg.mpr hx), hroot⟩, ?_⟩
  rintro y' ⟨hmod, hzero⟩
  exact unique y' ⟨by simpa using (nilpotent_of_parameter_dvd hz hmod).neg, hzero⟩

/-- Lift the quadratic root when the constant term changes from `ρ*a` to `ρ*(a+z)`. -/
theorem quadraticRootLift {z a ρ u : R} (hz : IsNilpotent z)
    (hu : u^2 + u + ρ*a = 0) (hd : IsUnit (2*u+1)) :
    ∃! v : R, z ∣ v-u ∧ v^2 + v + ρ*(a+z) = 0 := by
  let p : R[X] := X^2 + X + C (ρ * (a+z))
  have he (x : R) : p.eval x = x^2 + x + ρ*(a+z) := by simp [p]
  have hd' : IsUnit (p.derivative.eval u) := by
    simpa [p, derivative_X_pow, one_add_one_eq_two] using hd
  have he' : p.eval u = z*ρ := by rw [he]; linear_combination hu
  simpa only [he] using existsUnique_root_congr hz p (he' ▸ dvd_mul_right z ρ) hd'

/-- At zero the two quadratic roots lift with unit difference. -/
theorem quadraticRootsAtZero (z ρ : R) (hz : IsNilpotent z) :
    ∃ a b : R, z ∣ a ∧ z ∣ b+1 ∧
      a^2+a+ρ*z = 0 ∧ b^2+b+ρ*z = 0 ∧ IsUnit (a-b) := by
  obtain ⟨a, ⟨ha, ea⟩, _⟩ := quadraticRootLift (a := 0) (ρ := ρ) (u := 0) hz (by simp) (by simp)
  obtain ⟨b, ⟨hb, eb⟩, _⟩ := quadraticRootLift (a := 0) (ρ := ρ) (u := -1) hz (by ring)
    (by simpa only [mul_neg, mul_one, show -(2:R)+1 = -1 by ring] using isUnit_one.neg)
  simp only [sub_zero, zero_add] at ha ea eb
  rw [sub_neg_eq_add] at hb
  refine ⟨a, b, ha, hb, ea, eb, ?_⟩
  have : IsNilpotent (a-(b+1)) := nilpotent_of_parameter_dvd hz (dvd_sub ha hb)
  convert! this.isUnit_one_add using 1
  ring

/-- The derivative at the original quadratic generator squares to the discriminant. -/
theorem quadraticDerivative_isUnit {ρ u : R} (hu : u^2+u+ρ=0) (hdisc : IsUnit (1-4*ρ)) :
    IsUnit (2*u+1) := by
  apply (isUnit_pow_iff (n := 2) (by decide)).mp
  rwa [show (2*u+1)^2 = 1-4*ρ by linear_combination 4 * hu]

/-- The original quadratic generator has a unique lift at the endpoint one. -/
theorem quadraticRootAtOne {z ρ u : R} (hz : IsNilpotent z) (hu : u^2+u+ρ=0)
    (hderiv : IsUnit (2*u+1)) : ∃! v : R, z ∣ v-u ∧ v^2+v+ρ*(1+z)=0 :=
  quadraticRootLift hz (by simpa using hu) hderiv

/-- The unique root near one of a perturbed binomial is a unit. -/
theorem binomialRootLift {z v : R} (hz : IsNilpotent z) (m : ℕ) (hm : IsUnit (m : R))
    (hv : z ∣ v-1) : ∃! w : R, z ∣ w-1 ∧ w^m=v ∧ IsUnit w := by
  let p : R[X] := X^m - C v
  have he (x : R) : p.eval x = x^m-v := by simp [p]
  have hd : IsUnit (p.derivative.eval 1) := by simpa [p, derivative_X_pow] using hm
  have he₁ : z ∣ p.eval 1 := by simpa only [he, one_pow, neg_sub] using (dvd_neg.mpr hv)
  obtain ⟨w, ⟨hw, hw'⟩, unique⟩ := existsUnique_root_congr hz p he₁ hd
  have hu := (nilpotent_of_parameter_dvd hz hw).isUnit_add_one
  refine ⟨w, ⟨hw, sub_eq_zero.mp ((he w) ▸ hw'), by simpa using hu⟩, ?_⟩
  rintro w' ⟨hw', he', _⟩
  exact unique w' ⟨hw', by rw [he, he', sub_self]⟩

/-- The binomial is split near zero by scaling its roots of unity by this unit. -/
theorem binomialScalingAtZero (z β : R) (hz : IsNilpotent z) (m : ℕ) (hm : IsUnit (m : R)) :
    ∃ w : Rˣ, z ∣ (w:R)-1 ∧ (w:R)^m = 1+(β-1)*z := by
  obtain ⟨w, ⟨hw, he, hu⟩, _⟩ := binomialRootLift (v := 1+(β-1)*z) hz m hm
    ⟨β-1, by ring⟩
  exact ⟨hu.unit, hw, he⟩

/-- Near one the same operation transports the binomial with constant term `β`. -/
theorem binomialScalingAtOne (z : R) (β : Rˣ) (hz : IsNilpotent z) (m : ℕ)
    (hm : IsUnit (m : R)) :
    ∃ w : Rˣ, z ∣ (w:R)-1 ∧ (β:R) * (w:R)^m = 1+((β:R)-1)*(1+z) := by
  obtain ⟨w, ⟨hw, he, hu⟩, _⟩ :=
    binomialRootLift (v := 1 + (↑β⁻¹ : R)*((β:R)-1)*z) hz m hm
      ⟨(↑β⁻¹ : R)*((β:R)-1), by ring⟩
  refine ⟨hu.unit, hw, ?_⟩
  rw [hu.unit_spec, he, mul_add, ← mul_assoc, ← mul_assoc, β.mul_inv]
  ring

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
