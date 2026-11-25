import OAI.Computability.BorderVNP.BranchFiberSlices
import Mathlib.RingTheory.Nullstellensatz

/-! # Prime components of an isolated fiber

In the coordinate ring of an affine chart, the full list of output residuals and
hyperplanes has finite common zero locus. Consequently every prime containing
these residuals is maximal, which is the base-locus condition for the weighted cuts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {K σ A : Type*} [Field K] [IsAlgClosed K] [Finite σ] [CommRing A]

/-- A prime ideal of a polynomial ring over an algebraically closed field with finite
geometric zero set is a closed point. -/
theorem prime_isMaximal_of_finite_locus (P : Ideal (MvPolynomial σ K)) [hP : P.IsPrime]
    (hf : (zeroLocus K P).Finite) : P.IsMaximal := by
  classical
  let points := hf.toFinset
  let m (x : σ → K) := vanishingIdeal K {x}
  have hle : points.inf m ≤ P := by
    intro g hg
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) P]
    intro x hx
    have hx' : x ∈ points := hf.mem_toFinset.mpr hx
    exact (Finset.inf_le (f := m) hx' hg) x rfl
  obtain ⟨x, _, hx⟩ := hP.inf_le'.mp hle
  have hm : (m x).IsMaximal := inferInstanceAs (vanishingIdeal K {x}).IsMaximal
  exact (hm.eq_of_le hP.ne_top hx) ▸ hm

/-- A finite full-coefficient locus in an affine presentation gives precisely the prime
condition needed for slice descent. The ring presentation need only be surjective. -/
theorem prime_isMaximal_of_finite_coeff_locus (π : MvPolynomial σ K →+* A)
    (hπ : Function.Surjective π) (p : Polynomial A)
    (hf : (zeroLocus K ((Ideal.span (Set.range p.coeff)).comap π)).Finite)
    (P : Ideal A) (hP : P.IsPrime) (hp : ∀ n, p.coeff n ∈ P) : P.IsMaximal := by
  let := hP
  have hinc : Ideal.span (Set.range p.coeff) ≤ P := Ideal.span_le.mpr (Set.range_subset_iff.mpr hp)
  let := prime_isMaximal_of_finite_locus (P.comap π) (hf.subset
    (zeroLocus_anti_mono (Ideal.comap_mono hinc)))
  have hm : ((P.comap π).map π).IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hπ
    (fun _ hx ↦ show _ ∈ P from hx ▸ P.zero_mem)
  simpa [Ideal.map_comap_of_surjective π hπ] using hm

end Branch

end BorderVNP
end Computability
end OAI
