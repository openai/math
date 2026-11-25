import OAI.Computability.NearSquareRoot.KernelPassPartial
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointPairCost

/-! # Normalized Fourier endpoint on the two active halves of a label -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Matrix Finset OAI.LinearAlgebra.FiniteFourier KernelNormalization SynchronizedPair
noncomputable section

private def collapsePair (h : ℕ) :
    PrimeCommonPair 2 1 h ≃ₗ[ZMod 2] Bits h × Bits h where
  toFun x := (x.1 0,x.2 0)
  invFun z := (fun _ => z.1, fun _ => z.2)
  left_inv x := by ext c i <;> rw [Subsingleton.elim c 0]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def pairBits (h : ℕ) :
    PrimeCommonPair 2 1 h ≃ₗ[ZMod 2] Bits (h+h) :=
  (collapsePair h).trans (splitBits h h).symm

private theorem pair_dot {h : ℕ} (y x : PrimeCommonPair 2 1 h) :
    pairBits h y ⬝ᵥ pairBits h x =
      ∑ c, ∑ i, (x.1 c i * y.1 c i + x.2 c i * y.2 c i) := by
  change (∑ b, Fin.append (y.1 0) (y.2 0) b * Fin.append (x.1 0) (x.2 0) b) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  simp [Finset.sum_add_distrib,mul_comm]

variable {A h : ℕ} {R : Type*} [AddCommGroup R] [Module (ZMod 2) R]
    [FiniteDimensional (ZMod 2) R]

/-- The same two-half endpoint as in the prime rectangle identity, now using
normalized Walsh children on each axis and the two actual binary charts. -/
theorem Realizes.endpointPair_between
    (ey ex : Bits A ≃ₗ[ZMod 2] PrimeCommonPair 2 1 h × R) :
    Realizes (2*h) (((2 : ℂ)⁻¹ ^ h •
      endpointPartial (endpointPairFourier (f := 1) (h := h) binaryRoot (1 : (ZMod 2)ˣ)) R).submatrix
      ey ex) := by
  classical
  let l := (pairBits h).prodCongr (LinearEquiv.refl (ZMod 2) R)
  let cy := ey.trans l
  let cx := ex.trans l
  rw [two_mul]
  have hr := Realizes.partialChart cy cx
  convert hr using 1
  ext y x
  have hy : cy y = (pairBits h (ey y).1, (ey y).2) := rfl
  have hx : cx x = (pairBits h (ex x).1, (ex x).2) := rfl
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, endpointPartial,
    KernelPass.partialChart, hy, hx]
  by_cases e : (ex x).2 = (ey y).2
  · simp only [e, ↓reduceIte]
    rw [show (w : ℂ)^(h+h) = (2 : ℂ)⁻¹^h by rw [← two_mul, even_child_normalization], pair_dot]
    simp [endpointPairFourier, character]
  · simp [e, Ne.symm e]

theorem Realizes.endpointPair
    (e : Bits A ≃ₗ[ZMod 2] PrimeCommonPair 2 1 h × R) :
    Realizes (2*h) (((2 : ℂ)⁻¹ ^ h •
      endpointPartial (endpointPairFourier (f := 1) (h := h) binaryRoot (1 : (ZMod 2)ˣ)) R).submatrix
      e e) := Realizes.endpointPair_between e e

end
end KernelPass

end NearSquareRoot
end Computability
end OAI
