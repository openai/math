import OAI.Computability.BorderVNP.BranchFiberLocus
import OAI.Computability.BorderVNP.BranchCurveGraphPlace
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Isolation of a retained point of the weighted special fiber

A finite common zero locus of the chart equations and the special-fiber
cuts implies that every prime of the corresponding fiber is a closed
point. This remains true for any polynomial deformation with the same
constant terms.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

/-- For a deformation of finitely many cuts in an affine presentation, a
character at a retained point is minimal over the special-fiber ideal. -/
theorem isolated_point_of_finite_fiber {K R σ ι : Type*}
    [Field K] [IsAlgClosed K] [Finite σ] [CommRing R] [Algebra K R]
    (ρ : MvPolynomial σ K →+* R) (surj : Function.Surjective ρ)
    (D : ι → MvPolynomial σ K) (δ : ι → Polynomial R)
    (constant : ∀ i, (δ i).eval 0 = ρ (D i))
    (finite : {x ∈ zeroLocus K (RingHom.ker ρ) | ∀ i, eval x (D i) = 0}.Finite)
    (χ : R →ₐ[K] K) (retained : ∀ i, χ (ρ (D i)) = 0) :
    RingHom.ker (Polynomial.aevalTower χ 0) ∈
      (Ideal.span (Set.range δ) ⊔ Ideal.span {Polynomial.X}).minimalPrimes := by
  let m := RingHom.ker (Polynomial.aevalTower χ 0)
  let e := Polynomial.evalRingHom (0 : R)
  have esurj : Function.Surjective e := fun r => ⟨Polynomial.C r, Polynomial.eval_C⟩
  have hcomp : (Polynomial.aevalTower χ 0).toRingHom = χ.toRingHom.comp e := by
    apply Polynomial.ringHom_ext
    · intro r
      change (Polynomial.aevalTower χ 0) (Polynomial.C r) = χ ((Polynomial.C r).eval 0)
      rw [Polynomial.aevalTower_C, Polynomial.eval_C]
    · change (Polynomial.aevalTower χ 0) Polynomial.X = χ (Polynomial.X.eval 0)
      rw [Polynomial.aevalTower_X, Polynomial.eval_X, map_zero]
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective (Polynomial.aevalTower χ 0)
    fun r => ⟨algebraMap K _ r, (Polynomial.aevalTower χ 0).commutes r⟩
  refine ⟨⟨hm.isPrime, sup_le (Ideal.span_le.mpr (Set.range_subset_iff.mpr ?_))
    ((Ideal.span_le.mpr ∘ Set.singleton_subset_iff.mpr) (Polynomial.aevalTower_X χ 0))⟩, ?_⟩
  · intro i
    change (Polynomial.aevalTower χ 0).toRingHom (δ i) = 0
    rw [hcomp]
    change χ ((δ i).eval 0) = 0
    rw [constant, retained]
  · intro Q hQ hQm
    let :=  hQ.1
    have kerle : RingHom.ker e ≤ Q := by
      simpa [e, Polynomial.ker_evalRingHom] using (le_sup_right.trans hQ.2)
    let J := Q.map e
    have : J.IsPrime := Ideal.map_isPrime_of_surjective esurj kerle
    have hd (i : ι) : D i ∈ J.comap ρ := by
      have inc : Ideal.span (Set.range δ) ≤ Q := le_sup_left.trans hQ.2
      have mem : δ i ∈ Q := inc (Ideal.subset_span (Set.mem_range_self i))
      change ρ (D i) ∈ Q.map e
      rw [← constant]
      exact Ideal.mem_map_of_mem e mem
    have : (J.comap ρ).IsMaximal := prime_isMaximal_of_finite_locus (J.comap ρ)
      (finite.subset (fun x hx => ⟨fun p hp => hx p
        (show ρ p ∈ J from (RingHom.mem_ker.mp hp) ▸ J.zero_mem),
        fun i => hx (D i) (hd i)⟩))
    have hJ : ((J.comap ρ).map ρ).IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le surj
      (fun _ hx => show _ ∈ J from (RingHom.mem_ker.mp hx) ▸ J.zero_mem)
    have : J.IsMaximal := by simpa only [Ideal.map_comap_of_surjective ρ surj] using hJ
    have hQmax := Ideal.comap_isMaximal_of_surjective e esurj (K := J)
    rw [show J.comap e = Q from (Ideal.comap_map_of_surjective e esurj Q).trans
      (sup_eq_left.mpr kerle)] at hQmax
    exact (hQmax.eq_of_le hm.ne_top hQm).ge

end Branch

end BorderVNP
end Computability
end OAI
