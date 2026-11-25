import OAI.LinearAlgebra.FiniteFourier.PrimeAxisFiber
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.LinearAlgebra.Basis.Defs

/-! # The binomial generator on a positive prime axis

A linear coordinate equal to one ensures that the generator survives in every
fiber over a maximal ideal. If the fibers are reduced and a positive power of
the generator is scalar, that scalar is a unit, as is the generator itself.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Module

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- An element with a unit coordinate stays nonzero in each residue fiber. -/
theorem residueFiber_ne_zero_of_unit_coordinate (b : A →ₗ[R] R) {Y : A} (hY : IsUnit (b Y))
    (P : Ideal R) (hP : P ≠ ⊤) :
    Ideal.Quotient.mk (P.map (algebraMap R A)) Y ≠ 0 := by
  intro hz
  have hmem : Y ∈ P • (⊤ : Submodule R A) := by
    rw [Ideal.smul_top_eq_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hcoord : b Y ∈ P • (⊤ : Submodule R R) :=
    Submodule.smul_top_le_comap_smul_top P b hmem
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at hcoord
  exact hP (P.eq_top_of_isUnit_mem hcoord hY)

/-- The scalar power and its generator are both units. The fiber hypothesis
is intrinsic to the algebra and does not require the base ring itself to be reduced. -/
theorem isUnit_scalar_and_generator_of_reduced_fibers
    (hred : ∀ (P : Ideal R) [P.IsMaximal], IsReduced (A ⧸ P.map (algebraMap R A)))
    (b : A →ₗ[R] R) {Y : A} (hcoord : IsUnit (b Y)) {m : ℕ} (hm : 0 < m)
    {β : R} (hY : Y ^ m = algebraMap R A β) : IsUnit β ∧ IsUnit Y := by
  have hβ : IsUnit β := by
    by_contra h
    obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr h)
    let : P.IsMaximal := hP
    let : IsReduced (A ⧸ P.map (algebraMap R A)) := hred P
    let π := Ideal.Quotient.mk (P.map (algebraMap R A))
    have hzero : π Y ^ m = 0 := by
      rw [← map_pow, hY]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hmem)
    exact residueFiber_ne_zero_of_unit_coordinate b hcoord P hP.ne_top (eq_zero_of_pow_eq_zero hzero)
  refine ⟨hβ, isUnit_of_dvd_unit (dvd_pow_self Y hm.ne') ?_⟩
  rw [hY]
  exact hβ.map (algebraMap R A)

/-- In the prime cyclotomic quotient, a coordinate equal to one is sufficient:
separability supplies the reducedness of every residue fiber. -/
theorem primeAxis_isUnit_of_power_of_coord {p : ℕ} (hp : IsUnit (p : R)) {ι : Type*}
    (b : Basis ι R (AdjoinRoot (Polynomial.cyclotomic p R)))
    {Y : AdjoinRoot (Polynomial.cyclotomic p R)} (i : ι) (hi : b.repr Y i = 1)
    {m : ℕ} {β : R} (hm : 0 < m) (hY : Y ^ m = algebraMap R _ β) :
    IsUnit β ∧ IsUnit Y :=
  isUnit_scalar_and_generator_of_reduced_fibers (fun P _ => primeAxisFiber_isReduced p hp P)
    (b.coord i) (by rw [Basis.coord_apply, hi]; exact isUnit_one) hm hY

/-- The positive-list generator is the sum of the two distinct frequency-one
basis vectors. Its coordinates survive reduction in every characteristic,
including characteristic two. -/
theorem primeAxis_sum_basis_isUnit {p : ℕ} (hp : IsUnit (p : R)) {ι : Type*}
    (b : Basis ι R (AdjoinRoot (Polynomial.cyclotomic p R))) {i j : ι} (hij : i ≠ j)
    {m : ℕ} {β : R} (hm : 0 < m) (hY : (b i + b j) ^ m = algebraMap R _ β) :
    IsUnit β ∧ IsUnit (b i + b j) := by
  classical
  exact primeAxis_isUnit_of_power_of_coord hp b i (by simp [hij]) hm hY

end FiniteFourier
end LinearAlgebra
end OAI
