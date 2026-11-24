import OAI.Computability.VPVNP.ExtensionAmplification
import OAI.Computability.VPVNP.SpectralStrictComparison
import OAI.Computability.VPVNP.SpectralPolynomialBound
import OAI.Computability.VPVNP.StarGrowth
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Matching the prescribed generator values in an exact extension

Section 2.3 uses a compactness argument to test a finite list of generators.
If every spectral point misses a target, one polynomial supply dominates the
balanced monomial at every spectral point. Its contraction bound contradicts
the exponential growth of contractions of that monomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

open Filter Topology

variable {S ι : Type*} [CommSemiring S] [Preorder S]

/-- A comparison between all powers bounds their contracted growth. The supply
is evaluated as a polynomial in the chosen generators, so its monomial bounds
apply even to covectors acting jointly on all factors. -/
theorem contraction_budget_of_power_comparison
    (G : ι → S) (target : ι → ℝ) (Φ : S → ℝ)
    (hmono : Monotone Φ) (hnonneg : ∀ x, 0 ≤ Φ x)
    (hcopies : ∀ (n : ℕ) x, Φ ((n : S) * x) = (n : ℝ) * Φ x)
    (hpoly : ∀ P : MvPolynomial ι ℕ,
      Φ (P.eval₂ (Nat.castRingHom S) G) ≤ P.eval₂ (Nat.castRingHom ℝ) target)
    (M : S) (f : ℝ) (L K : ℕ) (hK : 0 < K) (P : MvPolynomial ι ℕ)
    (hlim : Tendsto (fun m : ℕ => (Φ (M ^ m)) ^ (m : ℝ)⁻¹) atTop (𝓝 f))
    (hcompare : ∀ m : ℕ, ((L : S) * M) ^ m ≤ (K : S) * (P.eval₂ (Nat.castRingHom S) G) ^ m) :
    (L : ℝ) * f ≤ P.eval₂ (Nat.castRingHom ℝ) target := by
  have hbudget : 0 ≤ P.eval₂ (Nat.castRingHom ℝ) target :=
    (hnonneg _).trans (hpoly P)
  apply limit_le_of_half_power_bound (Nat.cast_nonneg L) hbudget
    (Nat.cast_pos.mpr hK) (Filter.Eventually.of_forall fun m => hnonneg (M ^ m)) hlim
  apply Filter.Frequently.of_forall
  intro m
  have hp : Φ (P.eval₂ (Nat.castRingHom S) G ^ m) ≤ P.eval₂ (Nat.castRingHom ℝ) target ^ m := by
    simpa only [MvPolynomial.eval₂_pow] using hpoly (P ^ m)
  have h := hmono (hcompare m)
  rw [mul_pow, ← Nat.cast_pow, hcopies, hcopies, Nat.cast_pow] at h
  calc
    (L : ℝ) ^ m * (Φ (M ^ m) / 2) ≤ (L : ℝ) ^ m * Φ (M ^ m) :=
      mul_le_mul_of_nonneg_left (by linarith [hnonneg (M ^ m)]) (by positivity)
    _ ≤ _ := h.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg K))

private noncomputable def variantSupply {ι : Type*} (s : Finset ι) [DecidableEq s] (e : ℕ) (c : s × Bool → ℕ) :
    MvPolynomial ι ℕ :=
  ∑ j, (c j : MvPolynomial ι ℕ) * ∏ i : s, MvPolynomial.X (i : ι) ^ amplificationExponent e j i

private theorem eval_variantSupply {ι R : Type*} [CommSemiring R] (g : ι → R)
    (s : Finset ι) [DecidableEq s] (e : ℕ) (c : s × Bool → ℕ) :
    (variantSupply s e c).eval₂ (Nat.castRingHom R) g =
      ∑ j, (c j : R) * ∏ i : s, g i ^ amplificationExponent e j i := by
  simp [variantSupply]

variable [NoZeroDivisors S] [Nontrivial S] [CharZero S]

/-- Finite-generator matching in the proof of Theorem 2.4. A contraction
functional bounds all monomials by their target products. If the bound is
asymptotically attained on each balanced reference monomial, some spectral
point realizes every generator target simultaneously. -/
theorem exists_matching_spectral_point
    (H : OrderBounds S) (rank : S →+* ℕ) (hrank : Monotone rank)
    (G : ι → S) (hG : ∀ i, G i ≠ 0) (target : ι → ℝ) (ht : ∀ i, 0 < target i)
    (required : Finset ι) (hreq : required.Nonempty) (Φ : S → ℝ)
    (hmono : Monotone Φ) (hnonneg : ∀ x, 0 ≤ Φ x)
    (hadd : ∀ a b, Φ (a + b) ≤ Φ a + Φ b)
    (hcopies : ∀ (n : ℕ) x, Φ ((n : S) * x) = (n : ℝ) * Φ x)
    (hmonomial : ∀ d : ι →₀ ℕ, Φ (d.prod fun i n => G i ^ n) ≤ d.prod fun i n => target i ^ n)
    (hbalanced : ∀ s : Finset ι, required ⊆ s → ∀ e : ℕ, 0 < e →
      Tendsto (fun m : ℕ => Φ ((∏ i : s, G i ^ e) ^ m) ^ (m : ℝ)⁻¹)
        atTop (𝓝 (∏ i : s, target i ^ e))) :
    ∃ F : S →+* ℝ, Monotone F ∧ ∀ i, F (G i) = target i := by
  classical
  by_contra hnone
  have miss : ∀ f ∈ spectrumValues S, ∃ i, f (G i) ≠ target i := by
    rintro _ ⟨F, hF, rfl⟩
    by_contra! h
    exact hnone ⟨F, hF, h⟩
  have hpos (F : S →+* ℝ) (hF : Monotone F) (i : ι) : 0 < F (G i) := by
    have h := hF (H.one_le (hG i))
    rw [map_one] at h
    exact zero_lt_one.trans_le h
  obtain ⟨s, hs, δ, hδ, hgap⟩ := compact_finite_generator_gap (spectrumValues_isCompact H)
    (fun i f => f (G i)) target (fun i => continuous_apply (G i)) ht
    (fun _ ⟨F, hF, eq⟩ i => eq ▸ hpos F hF i) miss required
  let : Nonempty s := (hreq.mono hs).coe_sort
  let Ω := { F : S →+* ℝ // Monotone F }
  let v (F : Ω) (i : s) : ℝ := F.val (G i)
  have hgap' (F : Ω) : ∃ i : s, 1 + δ ≤ v F i / target i ∨ 1 + δ ≤ target i / v F i := by
    obtain ⟨i, hi, h⟩ := hgap F.val ⟨F.val, F.property, rfl⟩
    exact ⟨⟨i, hi⟩, h⟩
  obtain ⟨e, L, c, he, hL, _, hdom, hbudget⟩ :=
    finiteProfileAmplification (H := Ω) (fun i : s => target i) v (fun i => ht i) (fun (F : Ω) i => hpos F.val F.property i)
      δ hδ hgap'
  let M : S := ∏ i : s, G i ^ e
  let P := variantSupply s e c
  let Y := P.eval₂ (Nat.castRingHom S) G
  have hyStrict (F : S →+* ℝ) (hF : Monotone F) : F ((L : S) * M) < F Y := by
    obtain ⟨j, hj⟩ := hdom (⟨F, hF⟩ : Ω)
    have hterm (l : s × Bool) :
        0 ≤ (c l : ℝ) * ∏ i : s, F (G i) ^ amplificationExponent e l i :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (hpos F hF i).le _)
    have hle := Finset.single_le_sum (fun l _ => hterm l) (Finset.mem_univ j)
    simpa only [M, Y, P, eval_variantSupply, map_sum, map_prod, map_mul, map_natCast, map_pow, v]
      using hj.trans_le hle
  have hY : Y ≠ 0 := by
    intro hz
    let R := (Nat.castRingHom ℝ).comp rank
    have hm : Monotone R := by
      intro a b hab
      change (rank a : ℝ) ≤ (rank b : ℝ)
      exact_mod_cast hrank hab
    have hy := hyStrict R hm
    rw [hz, map_zero] at hy
    have hzero := hm (H.zero_le ((L : S) * M))
    rw [map_zero] at hzero
    exact hy.not_ge hzero
  obtain ⟨K, hK, hrestrict⟩ := strict_spectral_comparison H rank hrank hY hyStrict
  have hpoly (p : MvPolynomial ι ℕ) : Φ (p.eval₂ (Nat.castRingHom S) G) ≤ p.eval₂ (Nat.castRingHom ℝ) target :=
    polynomial_target_bound Φ G target hadd (fun n a => (hcopies n a).le) hmonomial p
  have h := contraction_budget_of_power_comparison G target Φ hmono hnonneg hcopies hpoly
    M (∏ i : s, target i ^ e) L K hK P (hbalanced s hs e he) hrestrict
  rw [show P = variantSupply s e c by rfl, eval_variantSupply] at h
  have hM : 0 < (∏ i : s, target i ^ e) :=
    Finset.prod_pos fun i _ => pow_pos (ht i) _
  have hLp : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  linarith [mul_pos hLp hM]

end Spectral

end VPVNP
end Computability
end OAI
