import OAI.Computability.VPVNP.CertificateReduction
import OAI.Computability.VPVNP.MacaulayRelations
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Prime-characteristic descent of the label equations

Section 8.2 applies prime reduction to the Macaulay matrix of all monomial
multiples of the integer equations. A characteristic-zero solution excludes the
row of one from its rational row space. The finite matrix argument supplies a
prime of controlled bit length with the same exclusion. Given the uniform
effective weak Nullstellensatz multiplier bound, the reduced equations then
have a common zero over the algebraic closure of that prime field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CertificateReduction

open MvPolynomial RadicalCertificate

variable {t : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Base change commutes with the entire bounded Macaulay matrix. -/
theorem macaulayMatrix_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (F : ι → MvPolynomial (Fin t) R) (H D : ℕ) :
    macaulayMatrix (fun i => map φ (F i)) H D = (macaulayMatrix F H D).map φ := by
  ext ⟨i, a⟩ j
  change (monomial a.val 1 * map φ (F i)).coeff j.val = φ ((monomial a.val 1 * F i).coeff j.val)
  rw [← coeff_map, map_mul, map_monomial, φ.map_one]

private theorem coefficientRow_one_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (D : ℕ) : (fun j : BoundedMonomial t D =>
      φ ((coefficientRow D (1 : MvPolynomial (Fin t) R)) j)) =
      coefficientRow D (1 : MvPolynomial (Fin t) S) := by
  funext j
  change φ ((1 : MvPolynomial (Fin t) R).coeff j.val) = _
  rw [← coeff_map, map_one]
  rfl

private theorem totalDegree_map_le {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (f : MvPolynomial (Fin t) R) : (map φ f).totalDegree ≤ f.totalDegree :=
  Finset.sup_mono (support_map_subset φ f)

/-- At the selected prime the constant polynomial one has no certificate with
multiplier degree at most `H`. This matrix statement needs no effective
Nullstellensatz hypothesis. -/
theorem exists_prime_one_notMem {K : Type*} [Field K] [CharZero K]
    (F : ι → MvPolynomial (Fin t) ℤ) (H d b : ℕ)
    (hdeg : ∀ i, (F i).totalDegree ≤ d) (hcoeff : ∀ i a, ((F i).coeff a).natAbs ≤ 2 ^ b)
    (x : Fin t → K) (hx : ∀ i, eval₂ (Int.castRingHom K) x (F i) = 0) :
    let a := Nat.clog 2 (H + d + 1) * t
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 ^ (2 * (a + Nat.clog 2 (a + b + 2)) + 1) ∧
      coefficientRow (H + d) (1 : MvPolynomial (Fin t) (ZMod p)) ∉
        Submodule.span (ZMod p) (Set.range (macaulayMatrix
          (fun i => map (Int.castRingHom (ZMod p)) (F i)) H (H + d)).row) := by
  let D := H + d
  let a := Nat.clog 2 (D + 1) * t
  let M := macaulayMatrix F H D
  let v := coefficientRow D (1 : MvPolynomial (Fin t) ℤ)
  have hQ : (fun j => (v j : ℚ)) ∉ Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row) := by
    intro hmem
    change (fun j => Int.castRingHom ℚ ((coefficientRow D (1 : MvPolynomial (Fin t) ℤ)) j))
      ∈ Submodule.span ℚ (Set.range ((macaulayMatrix F H D).map (Int.castRingHom ℚ)).row) at hmem
    rw [coefficientRow_one_map, ← macaulayMatrix_map] at hmem
    have hx' (i : ι) : aeval x (map (Int.castRingHom ℚ) (F i)) = 0 := by
      rw [aeval_def, eval₂_map]
      exact (Subsingleton.elim ((algebraMap ℚ K).comp (Int.castRingHom ℚ)) (Int.castRingHom K)) ▸ hx i
    have hzero := aeval_eq_zero_of_row_mem (fun i => map (Int.castRingHom ℚ) (F i))
      (fun i => (totalDegree_map_le _ _).trans (hdeg i)) 1 (by simp) hmem x hx'
    simp at hzero
  have hcard : Fintype.card (BoundedMonomial t D) ≤ 2 ^ a := calc
    _ ≤ (D + 1) ^ t := card_boundedMonomial_le t D
    _ ≤ (2 ^ Nat.clog 2 (D + 1)) ^ t := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = _ := (pow_mul _ _ _).symm
  obtain ⟨p, hp, hsize, hmem⟩ := exists_bounded_good_prime_of_notMem M v a b hcard
    (macaulayMatrix_natAbs_le F hcoeff) (fun j => (coefficientRow_one_natAbs_le j).trans Nat.one_le_two_pow) hQ
  refine ⟨p, hp, hsize, ?_⟩
  change (fun j => Int.castRingHom (ZMod p) ((coefficientRow D (1 : MvPolynomial (Fin t) ℤ)) j))
    ∉ Submodule.span (ZMod p) (Set.range ((macaulayMatrix F H D).map (Int.castRingHom (ZMod p))).row) at hmem
  rwa [coefficientRow_one_map, ← macaulayMatrix_map] at hmem

/-- A uniform weak certificate degree bound turns a failed Macaulay row test
over the base field into a common zero in the extension where the bound holds. -/
theorem commonZero_of_one_notMem {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : ι → MvPolynomial (Fin t) K) (H d : ℕ) (hdeg : ∀ i, (F i).totalDegree ≤ d)
    (hmem : coefficientRow (H + d) (1 : MvPolynomial (Fin t) K) ∉
      Submodule.span K (Set.range (macaulayMatrix F H (H + d)).row))
    (bound : WeakCertificateBound E ι t d H) : ∃ x : Fin t → E, ∀ i, aeval x (F i) = 0 := by
  by_contra hno
  let φ := algebraMap K E
  let G (i : ι) := map φ (F i)
  have hn : ¬ ∃ x : Fin t → E, ∀ i, eval x (G i) = 0 := by
    simpa only [G, eval_map, φ, aeval_def] using hno
  obtain ⟨A, hA, he⟩ := bound G (fun i => (totalDegree_map_le φ _).trans (hdeg i)) hn
  have hrow := coefficientRow_sum_mul_mem G A (H + d) hA
  rw [he, macaulayMatrix_map φ F, ← coefficientRow_one_map φ (H + d)] at hrow
  exact hmem (rowSpan_descent _ _ hrow)

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩

/-- The characteristic-zero case of the choice-of-characteristic step in
Theorem 8.1, conditional on the stated effective weak Nullstellensatz bound. -/
theorem exists_prime_solution_of_weakCertificateBound {K : Type*} [Field K] [CharZero K]
    (F : ι → MvPolynomial (Fin t) ℤ) (H d b : ℕ)
    (hdeg : ∀ i, (F i).totalDegree ≤ d) (hcoeff : ∀ i a, ((F i).coeff a).natAbs ≤ 2 ^ b)
    (x : Fin t → K) (hx : ∀ i, eval₂ (Int.castRingHom K) x (F i) = 0)
    (bound : ∀ p : Nat.Primes, WeakCertificateBound (AlgebraicClosure (ZMod p.val)) ι t d H) :
    let a := Nat.clog 2 (H + d + 1) * t
    ∃ p : Nat.Primes, p.val ≤ 2 ^ (2 * (a + Nat.clog 2 (a + b + 2)) + 1) ∧
      ∃ y : Fin t → AlgebraicClosure (ZMod p.val), ∀ i,
        eval₂ (Int.castRingHom (AlgebraicClosure (ZMod p.val))) y (F i) = 0 := by
  obtain ⟨p, hp, hsize, hmem⟩ := exists_prime_one_notMem F H d b hdeg hcoeff x hx
  let p' : Nat.Primes := ⟨p, hp⟩
  let : Fact p.Prime := ⟨hp⟩
  let E := AlgebraicClosure (ZMod p)
  obtain ⟨y, hy⟩ := commonZero_of_one_notMem (fun i => map (Int.castRingHom (ZMod p)) (F i))
    H d (fun i => (totalDegree_map_le _ _).trans (hdeg i)) hmem (bound p')
  refine ⟨p', hsize, y, fun i => ?_⟩
  have hi := hy i
  rw [aeval_def, eval₂_map] at hi
  exact (Subsingleton.elim ((algebraMap (ZMod p) E).comp (Int.castRingHom (ZMod p))) (Int.castRingHom E)) ▸ hi

end CertificateReduction

end VPVNP
end Computability
end OAI
