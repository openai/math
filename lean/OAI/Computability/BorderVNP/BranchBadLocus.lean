import OAI.Computability.BorderVNP.BranchDegreeRational
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Div

/-! # An effective hypersurface avoiding the bad generic fibers in §9.2

The rational map ψ and a nonzero regular function δ on its graph satisfy a bounded
relation. Remove all powers of the distinguished variable corresponding to δ. Its
constant coefficient is a nonzero polynomial on the target and its pullback is an
explicit multiple of δ in the graph algebra. This applies both to the chart boundary
and to the cleared Jacobian numerator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {m d : ℕ}

private theorem eval_split (g : Fin m → L) (δ : L) (W : MvPolynomial (Fin (m+1)) K) :
    Polynomial.eval₂ (aeval g).toRingHom δ (finSuccEquiv K m W) = aeval (Fin.cons δ g) W := by
  have he : (Polynomial.eval₂RingHom (aeval g).toRingHom δ).comp (finSuccEquiv K m).toRingHom =
      (aeval (Fin.cons δ g)).toRingHom := by
    apply ringHom_ext
    · intro k
      simp [finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [finSuccEquiv_X_zero]
      · simp [finSuccEquiv_X_succ]
  exact DFunLike.congr_fun he W

/-- From a relation in a nonzero graph function and a target map, extract a nonzero
equation cutting out the image of the zero locus of that function. The multiplier is a
polynomial in the graph function and target coordinates, so the identity specializes at
every graph point. -/
theorem bad_locus_of_relation (g : Fin m → L) (δ : L) (hδ : δ ≠ 0)
    (W : MvPolynomial (Fin (m+1)) K) (hW : W ≠ 0) (hz : aeval (Fin.cons δ g) W = 0) :
    ∃ f : MvPolynomial (Fin m) K, f ≠ 0 ∧ f.totalDegree ≤ W.totalDegree ∧
      ∃ q : MvPolynomial (Fin (m+1)) K, aeval g f = δ * aeval (Fin.cons δ g) q := by
  let split := finSuccEquiv K m
  let P := split W
  have hP : P ≠ 0 := (map_ne_zero_iff split split.injective).mpr hW
  obtain ⟨Q, he, hQ⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  simp only [map_zero, sub_zero] at he hQ
  have hf : Q.coeff 0 ≠ 0 := fun h => hQ (Polynomial.X_dvd_iff.mpr h)
  let ev := Polynomial.eval₂RingHom (aeval (R := K) g).toRingHom δ
  have hX : ev Polynomial.X = δ := Polynomial.eval₂_X _ _
  have hC (p) : ev (Polynomial.C p) = aeval g p := Polynomial.eval₂_C _ _
  have heval (V : MvPolynomial (Fin (m+1)) K) : ev (split V) = aeval (Fin.cons δ g) V :=
    eval_split g δ V
  have hzP : ev P = 0 := (heval W).trans hz
  have hzQ : ev Q = 0 := by
    rw [he, map_mul, map_pow, hX] at hzP
    exact (mul_eq_zero.mp hzP).resolve_left (pow_ne_zero _ hδ)
  have hdvd : split.symm Q ∣ W := by
    have hp : Q ∣ P := by rw [he]; exact dvd_mul_left Q _
    simpa [P] using map_dvd split.symm hp
  have hc : (split (split.symm Q)).coeff 0 ≠ 0 := by simpa using hf
  have hdeg := totalDegree_coeff_finSuccEquiv_add_le (split.symm Q) 0 hc
  change ((split (split.symm Q)).coeff 0).totalDegree + 0 ≤ _ at hdeg
  rw [split.apply_symm_apply, Nat.add_zero] at hdeg
  refine ⟨Q.coeff 0, hf, hdeg.trans (totalDegree_le_of_dvd_of_isDomain hdvd hW),
    split.symm (-Q.divX), ?_⟩
  have h := congrArg ev (Polynomial.X_mul_divX_add Q)
  rw [map_add, map_mul, hzQ, hX, hC] at h
  rw [← heval, split.apply_symm_apply, map_neg, mul_neg]
  exact eq_neg_of_add_eq_zero_right h

/-- A degree-bounded nonzero polynomial excludes all images of the exceptional set `δ = 0`
for an `m`-parameter rational map to `m` coordinates. -/
theorem rational_bad_locus [Infinite K] (x g : Fin m → L) (δ : L) (hδ : δ ≠ 0)
    (den : MvPolynomial (Fin m) K) (num : Fin (m+1) → MvPolynomial (Fin m) K)
    (hden : aeval x den ≠ 0) (hd : den.totalDegree ≤ d) (hn : ∀ i, (num i).totalDegree ≤ d)
    (hfrac : ∀ i, (Fin.cons δ g : Fin (m+1) → L) i * aeval x den = aeval x (num i)) :
    ∃ f : MvPolynomial (Fin m) K, f ≠ 0 ∧
      f.totalDegree ≤ perronSimplexBound (m+1) (d+1) ∧
      ∃ q : MvPolynomial (Fin (m+1)) K, aeval g f = δ * aeval (Fin.cons δ g) q := by
  obtain ⟨W, hW, hWd, hz⟩ := rational_perron_relation x (Fin.cons δ g) den num hden hd hn hfrac
  obtain ⟨f, hf, hfd, hq⟩ := bad_locus_of_relation g δ hδ W hW hz
  exact ⟨f, hf, hfd.trans hWd, hq⟩

end Branch

end BorderVNP
end Computability
end OAI
