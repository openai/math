import OAI.LinearAlgebra.FiniteFourier.PrimeQuery

/-! # Ordinary kernel of the quadratic multiplier on digit tuples

Each paired coordinate contributes one chirp on each side of a swapped
Fourier transform and a factor of the inverse radix.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K : Type*} [CommRing K] {ℓ : ℕ} [NeZero ℓ] {ζ : K}

variable {ι : Type*} [Fintype ι]
open scoped Classical

/-- A phase on a sum of digit exponents factors into coordinate phases. -/
theorem digitPhase_sum (hζ : IsPrimitiveRoot ζ ℓ) (f : ι → ZMod ℓ) :
    digitPhase hζ (∑ i, f i) = ∏ i, digitPhase hζ (f i) := by
  induction (Finset.univ : Finset ι) using Finset.induction with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

variable [Invertible (ℓ : K)]

/-- The ordinary kernel of the quadratic frequency multiplier, in paired digit coordinates. -/
noncomputable def primeTupleKernelRing (hζ : IsPrimitiveRoot ζ ℓ) (x y s t : ι → ZMod ℓ) : K :=
  (⅟ (ℓ : K)) ^ (2 * Fintype.card ι) *
    ∑ X : ι → ZMod ℓ, ∑ Z : ι → ZMod ℓ,
      digitPhase hζ (∑ i, ((x i - s i) * X i + (y i - t i) * Z i + X i * Z i))

private theorem singlePair_kernel (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (x y s t : ZMod ℓ) :
    (⅟ (ℓ : K))^2 * (∑ X : ZMod ℓ, ∑ Z : ZMod ℓ,
      digitPhase hζ ((x-s)*X + (y-t)*Z + X*Z)) =
    ⅟ (ℓ : K) * digitPhase hζ ((x-s)*(t-y)) := by
  have he := sum_quadratic_query_phase hζ 1 x y s t
  simp only [Units.val_one, one_mul, inv_one] at he
  rw [he]
  calc
    _ = (⅟ (ℓ : K) * (ℓ : K)) * (⅟ (ℓ : K) * digitPhase hζ ((x-s)*(t-y))) := by ring
    _ = _ := by rw [invOf_mul_self, one_mul]

/-- Fourier inversion on both tuples is a product of the one-pair kernels. -/
theorem primeTupleKernelRing_eq (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (x y s t : ι → ZMod ℓ) :
    primeTupleKernelRing hζ x y s t =
      (⅟ (ℓ : K)) ^ Fintype.card ι * digitPhase hζ (∑ i, (x i - s i) * (t i - y i)) := by
  let f (i : ι) (u v : ZMod ℓ) :=
    digitPhase hζ ((x i - s i) * u + (y i - t i) * v + u * v)
  have hsum :
      (∑ X : ι → ZMod ℓ, ∑ Z : ι → ZMod ℓ, ∏ i, f i (X i) (Z i)) =
        ∏ i, ∑ u : ZMod ℓ, ∑ v : ZMod ℓ, f i u v := by
    rw [Fintype.prod_sum (fun i u => ∑ v : ZMod ℓ, f i u v)]
    exact Finset.sum_congr rfl fun X _ => (Fintype.prod_sum (fun i v => f i (X i) v)).symm
  unfold primeTupleKernelRing
  simp_rw [digitPhase_sum]
  change _ * (∑ X : ι → ZMod ℓ, ∑ Z : ι → ZMod ℓ, ∏ i, f i (X i) (Z i)) = _
  rw [hsum, pow_mul]
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using
    Finset.prod_congr (s₁ := Finset.univ) rfl
      (fun i _ => singlePair_kernel hζ (x i) (y i) (s i) (t i))

/-- Input and output chirp factors and the swapped positive-sign Fourier phase. -/
theorem primeTupleKernelRing_eq_fourierPhase (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (x y s t : ι → ZMod ℓ) :
    primeTupleKernelRing hζ x y s t = (⅟ (ℓ : K)) ^ Fintype.card ι *
      digitPhase hζ (-(∑ i, x i * y i)) * digitPhase hζ (-(∑ i, s i * t i)) *
      digitPhase hζ (∑ i, (x i * t i + y i * s i)) := by
  rw [primeTupleKernelRing_eq, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

section Field
variable {E : Type*} [Field E] {ξ : E}

/-- The paired kernel with its usual field normalization. -/
noncomputable def primeTupleKernel (hξ : IsPrimitiveRoot ξ ℓ) (x y s t : ι → ZMod ℓ) : E :=
  letI := invertibleOfNonzero hξ.neZero'.out
  primeTupleKernelRing hξ x y s t

theorem primeTupleKernel_eq (hξ : IsPrimitiveRoot ξ ℓ) (x y s t : ι → ZMod ℓ) :
    primeTupleKernel hξ x y s t =
      (ℓ : E)⁻¹ ^ Fintype.card ι * digitPhase hξ (∑ i, (x i - s i) * (t i - y i)) := by
  let := invertibleOfNonzero hξ.neZero'.out
  simpa [primeTupleKernel, invOf_eq_inv] using primeTupleKernelRing_eq hξ x y s t

theorem primeTupleKernel_eq_fourierPhase (hξ : IsPrimitiveRoot ξ ℓ) (x y s t : ι → ZMod ℓ) :
    primeTupleKernel hξ x y s t = (ℓ : E)⁻¹ ^ Fintype.card ι *
      digitPhase hξ (-(∑ i, x i * y i)) * digitPhase hξ (-(∑ i, s i * t i)) *
      digitPhase hξ (∑ i, (x i * t i + y i * s i)) := by
  let := invertibleOfNonzero hξ.neZero'.out
  simpa [primeTupleKernel, invOf_eq_inv] using primeTupleKernelRing_eq_fourierPhase hξ x y s t
end Field

end FiniteFourier
end LinearAlgebra
end OAI
