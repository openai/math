import OAI.Computability.BorderVNP.CrossingRate
import OAI.Computability.BorderVNP.ModelBaseChange
import OAI.Computability.BorderVNP.ModelOrdinary
import OAI.Computability.BorderVNP.TransferRate

/-!
# The rate and characteristic quantifiers in Theorem 1.1

The absolute coefficient comes from the two rounded scales in §4. A single
small circuit at a sufficiently large length supplies a fixed shortening, to
which the stretch lemma can then be applied at *all* sufficiently large lengths.
The field extension argument in §2.1 subsequently transfers a single threshold
to every field in the chosen characteristic.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Rate
universe u

open Filter
open BorderVNP.Crossing

/-- The exponent coefficient after allowing for both floors in the §4 construction. -/
noncomputable def crossingConstant (c₀ c₁ c₂ : ℝ) : ℝ :=
  c₂ * (Real.sqrt (c₀ / 2) * (c₁ / 2) ^ (5 / 4 : ℝ))

/-- The rate coefficient depends only on the absolute constants chosen for §4. -/
theorem crossingConstant_pos {c₀ c₁ c₂ : ℝ} (h₀ : 0 < c₀) (h₁ : 0 < c₁) (h₂ : 0 < c₂) :
    0 < crossingConstant c₀ c₁ c₂ := by
  unfold crossingConstant
  positivity

/-- The last paragraph of §4.4. The stretch exponent may depend on the shortening
selected at one exceptional length. The final coefficient depends only on the
parameters of the crossing, even if the threshold depends on the characteristic. -/
theorem eventual_rate_of_single_shortening {c₀ c₁ c₂ : ℝ} (h₀ : 0 < c₀) (h₁ : 0 < c₁)
    (h₂ : 0 < c₂) (s : ℕ → ℕ) (shortening : Prop)
    (small : ∀ᶠ n : ℕ in atTop,
      (s n : ℝ) ≤ (2 : ℝ) ^ (c₂ * (width c₁ n * Real.sqrt (directions c₀ (width c₁ n)))) →
        shortening)
    (stretch : shortening → ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) ^ ε) ≤ s n) :
    ∀ᶠ n : ℕ in atTop, rate (crossingConstant c₀ c₁ c₂) n ≤ s n := by
  apply eventually_large_of_stretch
  intro hbad
  apply stretch
  obtain ⟨n, hn, hc, hw⟩ := (hbad.and_eventually (small.and (width_sqrt_directions h₀ h₁))).exists
  apply hc
  apply hn.le.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [crossingConstant, mul_assoc]
  exact mul_le_mul_of_nonneg_left hw.1 h₂.le

/-- A positive coefficient in the logarithmic rate beats every fixed polynomial
exponent. In particular it also excludes polynomial size with an arbitrary
multiplicative constant and length cutoff. -/
theorem superpolynomial_of_rate {c : ℝ} (hc : 0 < c) {s : ℕ → ℕ}
    (h : ∀ᶠ n : ℕ in atTop, rate c n ≤ s n) : VPVNP.EventuallySuperpolynomial s := by
  intro C _
  apply eventually_atTop.1
  filter_upwards [eventually_atTop.2 (eventually_pow_lt_rate hc C), h] with n hp hs
  exact_mod_cast hp.trans_le hs

/-- An explicit VNP family with the component rate separates VNP from the usual
full-coefficient border VP class on the same variable types. -/
theorem vnp_not_subset_of_rate {F : Type*} [Field F] {X : ℕ → Type} [∀ n, Fintype (X n)]
    (p : VPVNP.Family F X) (d : ℕ → ℕ) (hp : VPVNP.IsVNP p) {c : ℝ} (hc : 0 < c)
    (hsize : ∀ᶠ n : ℕ in atTop, rate c n ≤ borderSize (d n) (p n)) :
    ¬ {g : VPVNP.Family F X | VPVNP.IsVNP g} ⊆ {g | IsBorderVP g} := by
  intro incl
  exact not_isBorderVP_of_eventual_size (superpolynomial_of_rate hc hsize) (incl hp)

/-- Scalar extension gives a threshold for each characteristic before the field
is quantified. Ground estimates suffice over the rationals and the prime fields. -/
theorem uniform_of_prime_fields {σ : ℕ → Type*} (f : ∀ n, MvPolynomial (σ n) ℤ)
    (d : ℕ → ℕ) (c : ℝ)
    (zero : ∀ᶠ n : ℕ in atTop,
      rate c n ≤ borderSize (d n) (MvPolynomial.map (Int.castRingHom ℚ) (f n)))
    (prime : ∀ q : ℕ, ∀ hq : q.Prime, letI : Fact q.Prime := ⟨hq⟩
      ∀ᶠ n : ℕ in atTop,
        rate c n ≤ borderSize (d n) (MvPolynomial.map (Int.castRingHom (ZMod q)) (f n))) :
    ∀ q : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ (F : Type u) [Field F] [CharP F q],
      rate c n ≤ borderSize (d n) (MvPolynomial.map (Int.castRingHom F) (f n)) := by
  intro q
  have lift (K : Type) [Field K] [CharP K q]
      (h : ∀ᶠ n : ℕ in atTop,
        rate c n ≤ borderSize (d n) (MvPolynomial.map (Int.castRingHom K) (f n))) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ (F : Type u) [Field F] [CharP F q],
        rate c n ≤ borderSize (d n) (MvPolynomial.map (Int.castRingHom F) (f n)) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 h
    refine ⟨N, fun n hn F _ _ => ?_⟩
    rw [← borderSize_intCast_eq (K := K) (F := F) q (d n) (f n)]
    exact hN n hn
  by_cases hz : q = 0
  · subst q
    exact lift ℚ zero
  by_cases hp : q.Prime
  · let : Fact q.Prime := ⟨hp⟩
    exact lift (ZMod q) (prime q hp)
  · refine ⟨0, fun _ _ F _ _ => ?_⟩
    exact ((CharP.char_is_prime_or_zero F q).elim hp hz).elim

end Rate

end BorderVNP
end Computability
end OAI
