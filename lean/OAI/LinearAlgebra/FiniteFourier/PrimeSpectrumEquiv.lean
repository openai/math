import OAI.LinearAlgebra.FiniteFourier.PrimeQueryTuple

/-! # Fourier inversion for a pair of digit tuples

The additive character of a primitive root pairs each digit with its corresponding
frequency. Orthogonality on each coordinate gives the normalized negative-sign inverse.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open scoped Classical

/-- Two tuples of digits, used for both the ordinary and the frequency indices. -/
abbrev PrimeSpectrumDigits (ι : Type*) (ℓ : ℕ) := (ι → ZMod ℓ) × (ι → ZMod ℓ)

variable {ι : Type*} [Fintype ι] {ℓ : ℕ}

/-- The sum of the two coordinatewise digit pairings. -/
def primeSpectrumPair (x ω : PrimeSpectrumDigits ι ℓ) : ZMod ℓ :=
  ∑ i, (x.1 i * ω.1 i + x.2 i * ω.2 i)

theorem primeSpectrumPair_comm (x ω : PrimeSpectrumDigits ι ℓ) :
    primeSpectrumPair x ω = primeSpectrumPair ω x := by
  unfold primeSpectrumPair
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm (x.1 i), mul_comm (x.2 i)]

variable [NeZero ℓ] {K : Type*} [CommRing K] {ζ : K}

private theorem tupleOrthogonality (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (x y : ι → ZMod ℓ) :
    (∑ ω : ι → ZMod ℓ, digitPhase hζ (∑ i, ω i * (x i - y i))) =
      if x = y then (ℓ : K) ^ Fintype.card ι else 0 := by
  simp_rw [digitPhase_sum]
  rw [← Fintype.prod_sum (fun i (z : ZMod ℓ) => digitPhase hζ (z * (x i - y i)))]
  simp_rw [PrimeSpectrumOrthogonal.sum_eq, sub_eq_zero]
  split_ifs with h
  · subst y
    simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Row orthogonality for the Fourier transform on two digit tuples. -/
theorem primeSpectrum_orthogonality (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (x y : PrimeSpectrumDigits ι ℓ) :
    (∑ ω : PrimeSpectrumDigits ι ℓ, digitPhase hζ (primeSpectrumPair x ω - primeSpectrumPair y ω)) =
      if x = y then (ℓ : K) ^ (2 * Fintype.card ι) else 0 := by
  have phases (ω : PrimeSpectrumDigits ι ℓ) :
      primeSpectrumPair x ω - primeSpectrumPair y ω =
        (∑ i, ω.1 i * (x.1 i - y.1 i)) + ∑ i, ω.2 i * (x.2 i - y.2 i) := by
    rw [primeSpectrumPair, primeSpectrumPair, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [phases, AddChar.map_add_eq_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, tupleOrthogonality]
  by_cases h₁ : x.1 = y.1 <;> by_cases h₂ : x.2 = y.2 <;>
    simp [Prod.ext_iff, h₁, h₂, two_mul, pow_add]

private def spectrumForward (hζ : IsPrimitiveRoot ζ ℓ) :
    (PrimeSpectrumDigits ι ℓ → K) →ₗ[K] (PrimeSpectrumDigits ι ℓ → K) where
  toFun v ω := ∑ x, digitPhase hζ (primeSpectrumPair x ω) * v x
  map_add' v w := by
    ext ω
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext ω
    simp [Finset.mul_sum, mul_left_comm]

variable [Invertible (ℓ : K)]

private def spectrumInverse (hζ : IsPrimitiveRoot ζ ℓ)
    (v : PrimeSpectrumDigits ι ℓ → K) (x : PrimeSpectrumDigits ι ℓ) : K :=
  (⅟ (ℓ : K)) ^ (2 * Fintype.card ι) *
    ∑ ω, digitPhase hζ (-(primeSpectrumPair x ω)) * v ω

private theorem spectrum_leftInverse (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] :
    Function.LeftInverse (spectrumInverse (ι := ι) hζ) (spectrumForward hζ) := by
  intro v
  ext x
  change (⅟ (ℓ : K)) ^ (2 * Fintype.card ι) *
    (∑ ω, digitPhase hζ (-(primeSpectrumPair x ω)) *
      ∑ y, digitPhase hζ (primeSpectrumPair y ω) * v y) = v x
  have inner (ω : PrimeSpectrumDigits ι ℓ) :
      digitPhase hζ (-(primeSpectrumPair x ω)) *
        (∑ y, digitPhase hζ (primeSpectrumPair y ω) * v y) =
      ∑ y, digitPhase hζ (primeSpectrumPair y ω - primeSpectrumPair x ω) * v y := by
    rw [Finset.mul_sum]
    simp_rw [← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_eq_sub]
  simp_rw [inner]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, primeSpectrum_orthogonality, ite_mul, zero_mul]
  simp [← mul_assoc, ← mul_pow]

private theorem spectrum_rightInverse (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] :
    Function.RightInverse (spectrumInverse (ι := ι) hζ) (spectrumForward hζ) := by
  intro v
  ext ω
  let c : K := (⅟ (ℓ : K)) ^ (2 * Fintype.card ι)
  change (∑ x, digitPhase hζ (primeSpectrumPair x ω) *
    (c * ∑ ν, digitPhase hζ (-(primeSpectrumPair x ν)) * v ν)) = v ω
  have inner (x : PrimeSpectrumDigits ι ℓ) :
      digitPhase hζ (primeSpectrumPair x ω) *
        (∑ ν, digitPhase hζ (-(primeSpectrumPair x ν)) * v ν) =
      ∑ ν, digitPhase hζ (primeSpectrumPair ω x - primeSpectrumPair ν x) * v ν := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg,
      primeSpectrumPair_comm x ω, primeSpectrumPair_comm x ν]
  simp_rw [mul_left_comm _ c, inner]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, primeSpectrum_orthogonality, ite_mul, zero_mul]
  simp [c, ← mul_assoc, ← mul_pow]

/-- The positive-sign Fourier transform on both digit tuples, with its normalized inverse. -/
def primeSpectrumEquiv (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] :
    (PrimeSpectrumDigits ι ℓ → K) ≃ₗ[K] (PrimeSpectrumDigits ι ℓ → K) :=
  { spectrumForward hζ with
    invFun := spectrumInverse hζ
    left_inv := spectrum_leftInverse hζ
    right_inv := spectrum_rightInverse hζ }

theorem primeSpectrumEquiv_apply (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (v : PrimeSpectrumDigits ι ℓ → K) (ω : PrimeSpectrumDigits ι ℓ) :
    primeSpectrumEquiv hζ v ω = ∑ x, digitPhase hζ (primeSpectrumPair x ω) * v x := rfl

theorem primeSpectrumEquiv_symm_apply (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (v : PrimeSpectrumDigits ι ℓ → K) (x : PrimeSpectrumDigits ι ℓ) :
    (primeSpectrumEquiv hζ).symm v x = (⅟ (ℓ : K)) ^ (2 * Fintype.card ι) *
      ∑ ω, digitPhase hζ (-(primeSpectrumPair x ω)) * v ω := rfl

end

end

end FiniteFourier
end LinearAlgebra
end OAI
