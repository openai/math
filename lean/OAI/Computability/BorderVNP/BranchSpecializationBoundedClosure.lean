import OAI.Computability.BorderVNP.BranchSpecialization
import OAI.Computability.BorderVNP.BranchSpecializationHeight

/-!
# Specializing bounded-degree equations at a prime of controlled size

Lemma 9.1 uses one prime for every relation over the algebraic closure of the
residue field. The bound below depends on the parameter dimension and the degree
and height bounds of the coordinate map. It also avoids any prescribed nonzero
integer whose prime divisors are forbidden by the tensor identities.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace BranchSpecialization

open MvPolynomial
open scoped Matrix

/-- A bound on the binary exponent of the chosen prime. Here `h` is the number of
parameters, `d` bounds the coordinate degrees, `D` is the tested relation degree,
`b` bounds the binary logarithms of coefficient norms, and `e` bounds the
binary logarithm of the exclusion integer. -/
def primeExponent (h d D b e : ℕ) : ℕ :=
  let a := Nat.clog 2 (d * D + 1) * h
  2 * (a + Nat.clog 2 (a + b * D + e + 2)) + 1

/-- A characteristic-zero image-closure inclusion gives, at one prime avoiding the
exclusion, every relation up to the specified degree over every infinite field of that
characteristic. The target coordinate count does not enter the bound for the prime. -/
theorem exists_prime_preserving_bounded_equations {ι σ E : Type*}
    [Finite ι] [Fintype σ] [Field E] [CharZero E] (Y : ι → MvPolynomial σ ℤ) (c : ι → ℤ)
    (d D b e : ℕ) (z : ℤ) (hz : z ≠ 0) (hzbound : z.natAbs ≤ 2 ^ e)
    (hd : ∀ i, (Y i).totalDegree ≤ d) (hb : ∀ i, coefficientNorm (Y i) ≤ 2 ^ b)
    (hc : Int.castRingHom E ∘ c ∈ imageClosure (polynomialImage
      (fun i => map (Int.castRingHom E) (Y i)))) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 ^ primeExponent (Fintype.card σ) d D b e ∧
      ¬ (p : ℤ) ∣ z ∧ ∀ (K : Type*) [Field K] [CharP K p] [Infinite K],
      ∀ q : MvPolynomial ι K, q.totalDegree ≤ D →
        (∀ y ∈ polynomialImage (fun i => map (Int.castRingHom K) (Y i)), eval y q = 0) →
        eval (Int.castRingHom K ∘ c) q = 0 := by
  let f : ℚ →+* E := Rat.castHom E
  have hf : f.comp (Int.castRingHom ℚ) = Int.castRingHom E := Subsingleton.elim _ _
  have hq (i : ι) : (map (Int.castRingHom ℚ) (Y i)).totalDegree ≤ d :=
    (Finset.sup_mono (support_map_subset _ _)).trans (hd i)
  have he : f ∘ (Int.castRingHom ℚ ∘ c) = Int.castRingHom E ∘ c := by
    funext i
    exact DFunLike.congr_fun hf (c i)
  have hrow := rowExpression_of_mem_imageClosure_extension f D
    (fun i => map (Int.castRingHom ℚ) (Y i)) hq (Int.castRingHom ℚ ∘ c)
    (by simpa only [he, map_map, hf] using hc)
  rw [relationMatrix_map, pointRow_map] at hrow
  have hspan : ((Int.castRingHom ℚ) ∘ pointRow c D) ∈ Submodule.span ℚ
      (Set.range ((relationMatrix Y d D).map (Int.castRingHom ℚ)).row) := by
    rw [← range_vecMulLinear]
    exact hrow
  obtain ⟨p, hp, hbound, hnot, hK⟩ :=
    Specialization.exists_bounded_rowSpan_prime (relationMatrix Y d D) (pointRow c D) z
      (Nat.clog 2 (d * D + 1) * Fintype.card σ) (b * D) e
      (relationMatrix_row_bound σ d D) (relationMatrix_entry_bound Y d D b hb) hz hzbound hspan
  refine ⟨p, hp, hbound, hnot, ?_⟩
  intro K _ _ _ q hdegree hvan
  have hr := hK K
  rw [← range_vecMulLinear] at hr
  apply vanishes_of_rowExpression (d := d) _ _ _ q hdegree hvan
  rw [relationMatrix_map, pointRow_map]
  exact hr

end BranchSpecialization

end BorderVNP
end Computability
end OAI
