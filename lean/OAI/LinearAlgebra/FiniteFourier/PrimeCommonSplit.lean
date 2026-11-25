import OAI.LinearAlgebra.FiniteFourier.PrimeQueryProduct

/-! # Fourier inversion of an individual query power

The distinguished slot selected by the query and all its auxiliary slots
carry a quadratic phase. In the remaining slots, character orthogonality
gives the identity kernel.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

variable {C J U : Type*}

/-- The selected distinguished slot and all auxiliary slots in each column. -/
def primeQueryActiveSlot (j : J) : C × (Unit ⊕ U) → C × (J ⊕ U)
  | (c, .inl _) => (c, .inl j)
  | (c, .inr u) => (c, .inr u)

/-- The other distinguished slots in each column. -/
def primeQuerySpectatorSlot (j : J) : C × {j' : J // j' ≠ j} → C × (J ⊕ U)
  | (c, k) => (c, .inl k.val)

open scoped Classical

/-- Partition all slots according to whether query `j` acts on them. -/
def primeQuerySlotEquiv (j : J) :
    (C × (Unit ⊕ U)) ⊕ (C × {j' : J // j' ≠ j}) ≃ C × (J ⊕ U) where
  toFun := Sum.elim (primeQueryActiveSlot j) (primeQuerySpectatorSlot j)
  invFun
    | (c, .inl k) =>
      if h : k = j then .inl (c, .inl ()) else .inr (c, ⟨k, h⟩)
    | (c, .inr u) => .inl (c, .inr u)
  left_inv := by
    rintro (⟨c, _ | u⟩ | ⟨c, k, hk⟩) <;>
      simp [primeQueryActiveSlot, primeQuerySpectatorSlot, *]
  right_inv := by
    rintro ⟨c, k | u⟩
    · by_cases h : k = j <;> simp [h, primeQueryActiveSlot, primeQuerySpectatorSlot]
    · rfl

variable {ℓ : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] [Invertible (ℓ : K)] {ζ : K}

/-- Two unconstrained frequency digits produce the identity on their positions. -/
private theorem spectator_kernel (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (x y s t : ZMod ℓ) :
    (⅟ (ℓ : K)) ^ 2 * (∑ X : ZMod ℓ, ∑ Z : ZMod ℓ,
      digitPhase hζ ((x - s) * X + (y - t) * Z)) =
      if x = s ∧ y = t then 1 else 0 := by
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [mul_comm (x - s), mul_comm (y - t), digitPhase_orthogonality]
  by_cases hx : x = s <;> by_cases hy : y = t <;> simp [hx, hy, sub_eq_zero]
  rw [sq, mul_assoc, invOf_mul_cancel_left, invOf_mul_self]

private theorem active_kernel (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (a : (ZMod ℓ)ˣ)
    (x y s t : ZMod ℓ) :
    (⅟ (ℓ : K)) ^ 2 * (∑ X : ZMod ℓ, ∑ Z : ZMod ℓ,
      digitPhase hζ ((x - s) * X + (y - t) * Z + (a : ZMod ℓ) * X * Z)) =
        ⅟ (ℓ : K) * digitPhase hζ ((x - s) * ((a⁻¹ : (ZMod ℓ)ˣ) * (t - y))) := by
  rw [sum_quadratic_query_phase, mul_comm (digitPhase hζ _), sq, mul_assoc, invOf_mul_cancel_left]

/-- Fourier inversion of a phase diagonal in the pairs of coordinates
factors into the product of the individual normalized two-digit sums. -/
private theorem diagonal_kernel_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hζ : IsPrimitiveRoot ζ ℓ) (x y s t b : ι → ZMod ℓ) :
    (⅟ (ℓ : K)) ^ (2 * Fintype.card ι) *
      (∑ X : ι → ZMod ℓ, ∑ Z : ι → ZMod ℓ,
        digitPhase hζ (∑ i, ((x i - s i) * X i + (y i - t i) * Z i)) *
        digitPhase hζ (∑ i, b i * X i * Z i)) =
      ∏ i, ((⅟ (ℓ : K)) ^ 2 * ∑ X : ZMod ℓ, ∑ Z : ZMod ℓ,
        digitPhase hζ ((x i - s i) * X + (y i - t i) * Z + b i * X * Z)) := by
  let f (i : ι) (X Z : ZMod ℓ) :=
    digitPhase hζ ((x i - s i) * X + (y i - t i) * Z + b i * X * Z)
  simp_rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib, digitPhase_sum]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, pow_mul]
  congr 1
  change (∑ X : ι → ZMod ℓ, ∑ Z : ι → ZMod ℓ, ∏ i, f i (X i) (Z i)) =
    ∏ i, ∑ X : ZMod ℓ, ∑ Z : ZMod ℓ, f i X Z
  rw [Fintype.prod_sum (fun i X => ∑ Z : ZMod ℓ, f i X Z)]
  exact Finset.sum_congr rfl fun X _ => (Fintype.prod_sum (fun i Z => f i (X i) Z)).symm

variable [Fintype C] [Fintype J] [Fintype U]

/-- The inverse Fourier kernel of a nonzero query power is a chirp on the
active slots times the identity kernel on the spectator slots. -/
theorem primeCommonSplit_kernel (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (j : J) (a : (ZMod ℓ)ˣ)
    (x y s t : C × (J ⊕ U) → ZMod ℓ) :
    (⅟ (ℓ : K)) ^ (2 * Fintype.card (C × (J ⊕ U))) *
      (∑ X : C × (J ⊕ U) → ZMod ℓ, ∑ Z : C × (J ⊕ U) → ZMod ℓ,
        digitPhase hζ (∑ i, ((x i - s i) * X i + (y i - t i) * Z i)) *
        digitPhase hζ ((a : ZMod ℓ) * primeQueryExponent (Function.curry X) (Function.curry Z) j)) =
      (⅟ (ℓ : K)) ^ Fintype.card (C × (Unit ⊕ U)) *
        digitPhase hζ (∑ i : C × (Unit ⊕ U),
          (x (primeQueryActiveSlot j i) - s (primeQueryActiveSlot j i)) * (↑a⁻¹ : ZMod ℓ) *
            (t (primeQueryActiveSlot j i) - y (primeQueryActiveSlot j i))) *
        (if x ∘ primeQuerySpectatorSlot j = s ∘ primeQuerySpectatorSlot j ∧
          y ∘ primeQuerySpectatorSlot j = t ∘ primeQuerySpectatorSlot j then 1 else 0) := by
  let b : C × (J ⊕ U) → ZMod ℓ :=
    fun i => Sum.elim (fun k => if k = j then (a : ZMod ℓ) else 0) (fun _ => a) i.2
  have hq (X Z : C × (J ⊕ U) → ZMod ℓ) :
      (a : ZMod ℓ) * primeQueryExponent (Function.curry X) (Function.curry Z) j =
        ∑ i, b i * X i * Z i := by
    simp [b, primeQueryExponent, Fintype.sum_prod_type, Fintype.sum_sum_type,
      Finset.mul_sum, mul_add, ite_mul, mul_assoc]
  let g (i : C × (J ⊕ U)) := (⅟ (ℓ : K)) ^ 2 *
    ∑ X : ZMod ℓ, ∑ Z : ZMod ℓ,
      digitPhase hζ ((x i - s i) * X + (y i - t i) * Z + b i * X * Z)
  simp_rw [hq]
  rw [diagonal_kernel_product hζ x y s t b]
  change (∏ i, g i) = _
  rw [← (primeQuerySlotEquiv j).prod_comp g, Fintype.prod_sum_type]
  have hactive (i : C × (Unit ⊕ U)) :
      b (primeQueryActiveSlot j i) = a := by
    rcases i with ⟨c, u | u⟩ <;> simp [primeQueryActiveSlot, b]
  have hother (i : C × {k : J // k ≠ j}) :
      b (primeQuerySpectatorSlot (U := U) j i) = 0 := by
    simp [primeQuerySpectatorSlot, b, i.2.property]
  change (∏ i, g (primeQueryActiveSlot j i)) * (∏ i, g (primeQuerySpectatorSlot j i)) = _
  simp only [g, hactive, hother, zero_mul, add_zero, active_kernel, spectator_kernel]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← digitPhase_sum, Fintype.prod_boole]
  simp only [Function.comp_def, funext_iff, forall_and, mul_assoc]

end

end FiniteFourier
end LinearAlgebra
end OAI
