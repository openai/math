import OAI.Computability.BorderVNP.BranchSpecializationBoundedClosure
import OAI.Computability.BorderVNP.BranchDegree

/-!
# Characteristic-zero specialization of polynomial image closure

The separating-equation bound depends on the parameter dimension and coordinate
degree, independently of the target dimension. Thus Lemma 9.1 uses one prime for
the actual image-closure inclusion, with an explicit bit bound that can also
accommodate fixed arithmetic exclusions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace BranchSpecialization

open MvPolynomial VPVNP.RadicalCertificate

/-- Sufficient cutoff for testing the ideal of the polynomial image, obtained by
the quantitative monic relation and graph argument. -/
def separatingDegree (h d : ℕ) : ℕ := 2 * perronSimplexBound (h + 1) (d + 1)

/-- A bounded list of degrees suffices to detect membership in the whole image closure.
The target coordinate dimension can exceed the number of parameters by any amount. -/
theorem mem_imageClosure_of_bounded_equations {ι σ K : Type*} [Finite ι] [Fintype σ]
    [Field K] [Infinite K] (Y : ι → MvPolynomial σ K) (c : ι → K) {d : ℕ}
    (hd : ∀ i, (Y i).totalDegree ≤ d)
    (hb : ∀ q : MvPolynomial ι K, q.totalDegree ≤ separatingDegree (Fintype.card σ) d →
      (∀ y ∈ polynomialImage Y, eval y q = 0) → eval c q = 0) :
    c ∈ imageClosure (polynomialImage Y) := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin σ
  let Y' (i : ι) := rename e (Y i)
  have he : polynomialImage Y' = polynomialImage Y := polynomialImage_rename e Y
  have hd' (i : ι) : (Y' i).totalDegree ≤ d := (totalDegree_rename_le e _).trans (hd i)
  intro q hq
  by_contra hc
  have hq' : aeval Y' q = 0 := (vanishes_on_polynomialImage_iff _ _).1 (he.symm ▸ hq)
  obtain ⟨f, hdeg, hf, hfc⟩ := Branch.bounded_separating_relation Y' c hd' q hq' hc
  have hvan := (vanishes_on_polynomialImage_iff _ _).2 hf
  rw [he] at hvan
  exact one_ne_zero (hfc.symm.trans (hb f hdeg hvan))

/-- Lemma 9.1's image-closure transfer. From an integral point in the image closure
over any characteristic-zero field one obtains a single prime avoiding the prescribed
integer. The image-closure inclusion holds over every infinite field of that prime
characteristic, in particular over the algebraic closure of the residue field. -/
theorem exists_prime_preserving_imageClosure {ι σ E : Type*}
    [Finite ι] [Fintype σ] [Field E] [CharZero E] (Y : ι → MvPolynomial σ ℤ) (c : ι → ℤ)
    (d b e : ℕ) (z : ℤ) (hz : z ≠ 0) (hzbound : z.natAbs ≤ 2 ^ e)
    (hd : ∀ i, (Y i).totalDegree ≤ d) (hb : ∀ i, coefficientNorm (Y i) ≤ 2 ^ b)
    (hc : Int.castRingHom E ∘ c ∈ imageClosure (polynomialImage
      (fun i => map (Int.castRingHom E) (Y i)))) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 ^ primeExponent (Fintype.card σ) d
      (separatingDegree (Fintype.card σ) d) b e ∧ ¬ (p : ℤ) ∣ z ∧
      ∀ (K : Type*) [Field K] [CharP K p] [Infinite K],
        Int.castRingHom K ∘ c ∈ imageClosure (polynomialImage
          (fun i => map (Int.castRingHom K) (Y i))) := by
  obtain ⟨p, hp, hsize, hnot, hvan⟩ :=
    exists_prime_preserving_bounded_equations Y c d (separatingDegree (Fintype.card σ) d)
      b e z hz hzbound hd hb hc
  refine ⟨p, hp, hsize, hnot, ?_⟩
  intro K _ _ _
  apply mem_imageClosure_of_bounded_equations (d := d) _ _ _ (hvan K)
  exact fun i => (Finset.sup_mono (support_map_subset _ _)).trans (hd i)

end BranchSpecialization

end BorderVNP
end Computability
end OAI
