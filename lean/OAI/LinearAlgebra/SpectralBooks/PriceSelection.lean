import OAI.LinearAlgebra.SpectralBooks.Doubling
import OAI.LinearAlgebra.SpectralBooks.Spectrum
import OAI.LinearAlgebra.SpectralBooks.StrictComparison

/-!
# Doubling via the normalized spectrum

The rank bound makes the space of normalized spectral points compact. On the
multiplicative monoid of nonzero tensors, taking logarithms gives additive
real-valued maps. The subsequent selection argument uses the restriction
expansion from strict comparison and the permutation-stretch estimate.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section
open scoped NNReal

variable {A : Type*} [CommSemiring A] {res : A → A → Prop} {P : Submonoid A}

/-- The log price is nonnegative because every nonzero tensor restricts to the unit. -/
theorem one_le_spectral_value (f : normalizedSpectrum res) {t : A} (ht : res 1 t) :
    1 ≤ f.val t := by
  simpa only [f.property.2.1] using f.property.2.2.2.2 1 t ht

/-- The nonzero tensor classes use tensor product as their additive operation.
The logarithm is base two, as in the manuscript. -/
def spectralLogHom (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res) :
    Additive P →+ ℝ where
  toFun x := Real.logb 2 (f.val x.toMul.val : ℝ)
  map_zero' := by simp [f.property.2.1]
  map_add' x y := by
    have hpos (t : P) : (f.val t.val : ℝ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_spectral_value f (hunit t))).ne'
    simp only [toMul_add, Submonoid.coe_mul, f.property.2.2.2.1, NNReal.coe_mul]
    exact Real.logb_mul (hpos x.toMul) (hpos y.toMul)

theorem spectralLogHom_nonneg (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res)
    (x : Additive P) : 0 ≤ spectralLogHom hunit f x := by
  apply Real.logb_nonneg (by norm_num)
  exact_mod_cast one_le_spectral_value f (hunit x.toMul)

theorem continuous_spectralLogHom (hunit : ∀ t : P, res 1 t) (x : Additive P) :
    Continuous (fun f : normalizedSpectrum res => spectralLogHom hunit f x) :=
  continuous_log_price (hunit x.toMul)

/-- Every normalized point assigns log price one to the full binary diagonal. -/
theorem spectralLogHom_two (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res)
    (h₂ : (2 : A) ∈ P) :
    spectralLogHom hunit f (Additive.ofMul (⟨2, h₂⟩ : P)) = 1 := by
  change Real.logb 2 (f.val 2 : ℝ) = 1
  have htwo : f.val 2 = (2 : ℝ≥0) := map_ofNat (normalizedSpectrum.toRingHom f) 2
  rw [htwo]
  exact Real.logb_self_eq_one (by norm_num)

/-- A spectral price is a common positive multiple of a normalized log
evaluation, or the zero price of a collapsed placement. -/
def IsSpectralPrice (hunit : ∀ t : P, res 1 t) (g : Additive P →+ ℝ) : Prop :=
  g = 0 ∨ ∃ (f : normalizedSpectrum res) (c : ℝ), 0 < c ∧ g = c • spectralLogHom hunit f

theorem IsSpectralPrice.nonneg {hunit : ∀ t : P, res 1 t} {g : Additive P →+ ℝ}
    (hg : IsSpectralPrice hunit g) (t : Additive P) : 0 ≤ g t := by
  rcases hg with rfl | ⟨f, c, hc, rfl⟩
  · rfl
  · exact mul_nonneg hc.le (spectralLogHom_nonneg hunit f t)

theorem IsSpectralPrice.mono {hunit : ∀ t : P, res 1 t} {g : Additive P →+ ℝ}
    (hg : IsSpectralPrice hunit g) {x y : Additive P} (hxy : res x.toMul.val y.toMul.val) :
    g x ≤ g y := by
  rcases hg with rfl | ⟨f, c, hc, rfl⟩
  · rfl
  · apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_spectral_value f (hunit x.toMul))
    · exact_mod_cast f.property.2.2.2.2 _ _ hxy

/-- The price selected from the actual normalized spectrum. The inputs from
tensor theory are finite rank, strict comparison and the ordinary-sum estimate
on positive powers of a diagonal times private products; all numerical
amplification, denominator clearing and compactness arguments are proved. -/
theorem spectral_price_of_permutation_stretch
    (hunit : ∀ t : P, res 1 t) (h₂ : (2 : A) ∈ P)
    (hfinite : ∀ t : A, ∃ n : ℕ, res t n)
    (hne : (normalizedSpectrum res).Nonempty)
    (ordinarySum : Additive P → (L : ℕ) → (Fin L → Additive P) → Prop)
    (compare : ExpandedStrictComparison (Set.range (spectralLogHom hunit))
      (fun x y => res x.toMul.val y.toMul.val) ordinarySum)
    (G : AddSubmonoid (Additive P)) (Δ u : Additive P) (hu : u ∈ G)
    (a b c : Additive P →+ ℝ) (ha : IsSpectralPrice hunit a)
    (hb : IsSpectralPrice hunit b) (hc : IsSpectralPrice hunit c)
    (lam C : ℝ) (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hU : 0 < (lam • a + b + c) u)
    (stretch : ∀ x ∈ G, ∀ (m L : ℕ) (Z : Fin L → Additive P), 0 < m →
      ordinarySum (m • (Δ + x)) L Z → ∃ l,
        (lam • a + b + c) (m • (Δ + x)) ≤
          (lam • a + b + c) (Z l) + C * Real.logb 2 L) :
    ∃ g : Additive P →+ ℝ, IsSpectralPrice hunit g ∧
      (∀ t, g t ≤ (lam • a + b + c) t) ∧ ∀ t ∈ G, g t = (lam • a + b + c) t := by
  classical
  let h := lam • a + b + c
  let : CompactSpace (normalizedSpectrum res) :=
    isCompact_iff_compactSpace.mp (isCompact_normalizedSpectrum res hfinite)
  let : Nonempty (normalizedSpectrum res) := hne.to_subtype
  have hh (t : Additive P) : 0 ≤ h t :=
    add_nonneg (add_nonneg (mul_nonneg hlam (ha.nonneg t)) (hb.nonneg t)) (hc.nonneg t)
  have hmono {x y : Additive P} (hxy : res x.toMul.val y.toMul.val) : h x ≤ h y :=
    add_le_add (add_le_add (mul_le_mul_of_nonneg_left (ha.mono hxy) hlam) (hb.mono hxy))
      (hc.mono hxy)
  have hfull (f : normalizedSpectrum res) : ∃ t, 0 < spectralLogHom hunit f t := by
    refine ⟨Additive.ofMul (⟨2,h₂⟩ : P), ?_⟩
    rw [spectralLogHom_two]
    norm_num
  obtain ⟨f, d, hd, hle, heq⟩ := select_spectral_price_of_finite_comparison
    (spectralLogHom hunit) h G Δ u (continuous_spectralLogHom hunit)
    (spectralLogHom_nonneg hunit) hh hu hU hfull (by
      intro x hx J Y hcover
      obtain ⟨i₀, _⟩ := hcover (Classical.choice inferInstance)
      apply finite_comparison_of_ordinary_sum compare h hmono hC (stretch x hx) (Fin.pos i₀) Y
      rintro _ ⟨q, rfl⟩
      exact hcover q)
  exact ⟨d • spectralLogHom hunit f, Or.inr ⟨f, d, hd, rfl⟩, hle, heq⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
