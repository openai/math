import OAI.Computability.NearSquareRoot.KernelBinaryQueries
import OAI.Computability.NearSquareRoot.KernelPassFrequency

/-! # Diagonal sign passes and exchange of the two binary halves -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryQuery
open OAI.LinearAlgebra.FiniteFourier KernelPass KernelNormalization Matrix Finset SynchronizedPadding
noncomputable section

variable {m u : ℕ}

def splitLinear (m u : ℕ) : Bits (Arity m u) ≃ₗ[ZMod 2] Paired m u where
  __ := halves m u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def swapHalves (m u : ℕ) : Bits (Arity m u) ≃ₗ[ZMod 2] Bits (Arity m u) :=
  (splitLinear m u).trans ((LinearEquiv.prodComm _ _ _).trans (splitLinear m u).symm)

@[simp] theorem halves_swap (x : Bits (Arity m u)) :
    halves m u (swapHalves m u x) = ((halves m u x).2, (halves m u x).1) :=
  (splitLinear m u).apply_symm_apply _

@[simp] theorem swap_twice (x : Bits (Arity m u)) : swapHalves m u (swapHalves m u x) = x := by
  apply (halves m u).injective
  simp

def phaseBit (x : Bits (Arity m u)) : ZMod 2 :=
  -(∑ a, (halves m u x).1 a * (halves m u x).2 a)

def chirp (m u : ℕ) : Local (Arity m u) := diagonal (character ∘ phaseBit)

private theorem swapped_axis (y x : Bits (Arity m u)) :
    walshColumn (Arity m u) (swapHalves m u y) x = (2 : ℂ)⁻¹ ^ (m+u) *
      character (∑ a, ((halves m u x).1 a * (halves m u y).2 a + (halves m u x).2 a * (halves m u y).1 a)) := by
  unfold walshColumn
  rw [axis_character, ← dot_halves, primeSpectrumPair_comm, primeSpectrumPair, halves_swap]
  congr 1
  simpa only [two_mul, Arity] using even_child_normalization (m+u)

theorem product_eq_signed {m u : ℕ} (hm : m ≡ 1 [MOD 2]) :
    (List.ofFn (query (m:=m) (u:=u))).prod =
      chirp m u * (pushAddress (swapHalves m u) * walshColumn (Arity m u)) * chirp m u := by
  ext y x
  rw [product_entry hm, primeTupleKernelRing_eq_fourierPhase, chirp, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have sw (z : Bits (Arity m u)) : y = swapHalves m u z ↔ z = swapHalves m u y := by
    constructor <;> rintro rfl <;> simp
  rw [Matrix.mul_apply]
  simp only [pushAddress, sw, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  rw [swapped_axis]
  simp only [Index, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin,
    Nat.one_mul, Nat.cast_ofNat, invOf_eq_inv, Function.comp_apply, phaseBit, character]
  ring

@[simp] theorem chirp_sq (m u : ℕ) : chirp m u * chirp m u = 1 := by
  rw [chirp, diagonal_mul_diagonal]
  ext y x
  by_cases e : y = x
  · subst x
    rcases character_sign (phaseBit y) with h | h <;> simp [h]
  · simp [e]

@[simp] theorem swap_sq (m u : ℕ) :
    pushAddress (swapHalves m u) * pushAddress (swapHalves m u) = 1 := by
  rw [← pushAddress_comp]
  ext y x
  simp [pushAddress, Matrix.one_apply]

/-- Two local signs and a single wire permutation recover the normalized
Walsh column matrix from the product of the queries. -/
theorem recover {m u : ℕ} (hm : m ≡ 1 [MOD 2]) :
    walshColumn (Arity m u) = pushAddress (swapHalves m u) * chirp m u *
      (List.ofFn (query (m:=m) (u:=u))).prod * chirp m u := by
  rw [product_eq_signed hm]
  simp only [mul_assoc, chirp_sq, mul_one]
  simp only [← mul_assoc, chirp_sq, swap_sq, one_mul]

end
end BinaryQuery

end NearSquareRoot
end Computability
end OAI
