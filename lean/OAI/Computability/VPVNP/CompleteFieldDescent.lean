import OAI.Computability.VPVNP.CircuitSize
import OAI.Computability.VPVNP.Hamiltonian
import OAI.Computability.VPVNP.PermanentPadding
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod

/-!
# Uniformity across fields of a fixed characteristic

Section 15.1 of *VP and VNP differ over every field* proves its bounds for the
Hamiltonian cycle and permanent over an algebraic closure of the prime field.
The sums defining these polynomials commute with coefficient maps. Thus the
same threshold and exponent in a bound over that closure apply to every field
of the given characteristic, even when circuits use arbitrary constants.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

@[simp] theorem map_hamiltonianCyclePolynomial (f : R →+* S) (m : ℕ) :
    map f (hamiltonianCyclePolynomial R m) = hamiltonianCyclePolynomial S m := by
  simp only [hamiltonianCyclePolynomial, map_sum, map_prod, map_X]

@[simp] theorem map_permanentPolynomial (f : R →+* S) (m : ℕ) :
    map f (permanentPolynomial R m) = permanentPolynomial S m := by
  simp only [permanentPolynomial_eq_sum, map_sum, map_prod, map_X]

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F]

/-- Every integer polynomial has minimum gate count over an algebraically closed
field among fields of the same characteristic. This includes characteristic zero. -/
theorem circuitSize_intCast_descent {σ : Type*} (q : ℕ) [CharP K q] [CharP F q]
    (P : MvPolynomial σ ℤ) :
    circuitSize (map (Int.castRingHom K) P) ≤ circuitSize (map (Int.castRingHom F) P) := by
  have through (k : Type) [Field k] [Algebra k K] [Algebra k F] :
      circuitSize (map (Int.castRingHom K) P) ≤ circuitSize (map (Int.castRingHom F) P) := by
    have hK : (algebraMap k K).comp (Int.castRingHom k) = Int.castRingHom K := Subsingleton.elim ..
    have hF : (algebraMap k F).comp (Int.castRingHom k) = Int.castRingHom F := Subsingleton.elim ..
    simpa only [map_map, hK, hF] using
      circuitSize_descent_le (K := K) (F := F) (map (Int.castRingHom k) P)
  rcases CharP.char_is_prime_or_zero K q with hp | rfl
  · have : Fact q.Prime := ⟨hp⟩
    let := ZMod.algebra K q
    let := ZMod.algebra F q
    exact through (ZMod q)
  · have := CharP.charP_to_charZero K
    have := CharP.charP_to_charZero F
    exact through ℚ

/-- For an integer family, a lower bound over one algebraically closed field
supplies a single threshold before quantifying over all fields of the characteristic. -/
theorem circuitSize_intCast_uniform_bound {σ : ℕ → Type*} (P : (n : ℕ) → MvPolynomial (σ n) ℤ)
    (q C N : ℕ) [CharP K q]
    (h : ∀ n ≥ N, n ^ C < circuitSize (map (Int.castRingHom K) (P n))) :
    ∀ n ≥ N, ∀ (F : Type*) [Field F] [CharP F q],
      n ^ C < circuitSize (map (Int.castRingHom F) (P n)) := by
  intro n hn F _ _
  exact (h n hn).trans_le (circuitSize_intCast_descent q (P n))

/-- Comparison of directed Hamiltonian-cycle circuit sizes at the same order. -/
theorem hamiltonianCyclePolynomial_size_descent (q m : ℕ) [CharP K q] [CharP F q] :
    circuitSize (hamiltonianCyclePolynomial K m) ≤ circuitSize (hamiltonianCyclePolynomial F m) := by
  simpa only [map_hamiltonianCyclePolynomial] using
    circuitSize_intCast_descent (K := K) (F := F) q (hamiltonianCyclePolynomial ℤ m)

/-- Comparison of permanent circuit sizes at the same order. Scalar descent
applies in every characteristic, including characteristic two. -/
theorem permanentPolynomial_size_descent (q m : ℕ) [CharP K q] [CharP F q] :
    circuitSize (permanentPolynomial K m) ≤ circuitSize (permanentPolynomial F m) := by
  simpa only [map_permanentPolynomial] using
    circuitSize_intCast_descent (K := K) (F := F) q (permanentPolynomial ℤ m)

/-- A threshold for Hamiltonian cycles over the algebraic closure works uniformly
for every field of its characteristic. -/
theorem hamiltonianCyclePolynomial_uniform_bound (q C N : ℕ) [CharP K q]
    (h : ∀ m ≥ N, m ^ C < circuitSize (hamiltonianCyclePolynomial K m)) :
    ∀ m ≥ N, ∀ (F : Type*) [Field F] [CharP F q],
      m ^ C < circuitSize (hamiltonianCyclePolynomial F m) := by
  intro m hm F _ _
  exact (h m hm).trans_le (hamiltonianCyclePolynomial_size_descent q m)

/-- A threshold for the permanent over the algebraic closure works uniformly
for every field of its characteristic. -/
theorem permanentPolynomial_uniform_bound (q C N : ℕ) [CharP K q]
    (h : ∀ m ≥ N, m ^ C < circuitSize (permanentPolynomial K m)) :
    ∀ m ≥ N, ∀ (F : Type*) [Field F] [CharP F q],
      m ^ C < circuitSize (permanentPolynomial F m) := by
  intro m hm F _ _
  exact (h m hm).trans_le (permanentPolynomial_size_descent q m)

end VPVNP
end Computability
end OAI
