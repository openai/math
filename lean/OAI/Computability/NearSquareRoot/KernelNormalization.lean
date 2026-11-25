import OAI.Computability.NearSquareRoot.SynchronizedPair
import OAI.LinearAlgebra.FiniteFourier.PrimeTransformPhase
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonKernel

/-! # Normalizing the binary query kernel

Each pass on an axis is a tensor of the actual normalized two-point Walsh
matrix. Its power of two is dyadic at every even child width. The product
of the normalizations of the endpoint calls supplies the whole common
kernel normalization, including after splitting the axes between endpoints. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelNormalization

open OAI.LinearAlgebra.FiniteFourier SynchronizedPair Matrix Finset
noncomputable section

theorem binaryRoot : IsPrimitiveRoot (-1 : ℂ) 2 := IsPrimitiveRoot.neg_one 0 (by decide)

def character (z : ZMod 2) : ℂ := digitPhase binaryRoot z

def axis {f : ℕ} (x y : Fin f → ZMod 2) : ℂ :=
  ∏ c, walsh (x c) (y c)

theorem walsh_character (x y : ZMod 2) : walsh x y = (w : ℂ) * character (x*y) := by
  fin_cases x <;> fin_cases y
  · change (w : ℂ) = (w : ℂ) * (-1)^0; simp
  · change (w : ℂ) = (w : ℂ) * (-1)^0; simp
  · change (w : ℂ) = (w : ℂ) * (-1)^0; simp
  · change -(w : ℂ) = (w : ℂ) * (-1)^1; simp

theorem axis_character {f : ℕ} (x y : Fin f → ZMod 2) :
    axis x y = (w : ℂ)^f * character (∑ c, x c*y c) := by
  simp [axis, walsh_character, character, digitPhase_sum, prod_mul_distrib]

theorem normalization_pair : (w : ℂ)^2 = (2 : ℂ)⁻¹ := by
  rw [w, Complex.ofReal_inv, inv_pow]
  congr 1
  norm_cast
  exact Real.sq_sqrt (by norm_num)

theorem even_child_normalization (h : ℕ) :
    (w : ℂ)^(2*h) = (2 : ℂ)⁻¹ ^ h := by rw [pow_mul, normalization_pair]

/-- Every endpoint can use normalized children. The number of left and right
endpoint axes can differ, provided their sum is twice the common dimension. -/
theorem endpoints_normalization {l r D f : ℕ} (h : l+r=2*D) :
    ((w : ℂ)^f)^l * ((w : ℂ)^f)^r = (2 : ℂ)⁻¹ ^ (f*D) := by
  rw [← pow_add, h, ← pow_mul, show f*(2*D)=2*(f*D) by ring, even_child_normalization]

/-- All phases left outside the Walsh axis calls have modulus one and are
implemented by an optional sign change. -/
theorem character_sign (z : ZMod 2) : character z = 1 ∨ character z = -1 := by
  fin_cases z
  · left; change (-1 : ℂ)^0 = 1; simp
  · right; change (-1 : ℂ)^1 = -1; simp

/-- Entrywise identity for the positive-sign transform used by spectral repair.
The two endpoint phases and the wire exchange suffice for the normalized target. -/
theorem query_is_normalized {k : ℕ} (x y s t : Fin k → ZMod 2) :
    primeTupleKernel binaryRoot x y s t =
      character (-(∑ c, x c*y c)) * character (-(∑ c, s c*t c)) *
        axis x t * axis y s := by
  rw [primeTupleKernel_eq_fourierPhase, axis_character, axis_character,
    sum_add_distrib, AddChar.map_add_eq_mul]
  change _ = _ * _ * (_ * digitPhase binaryRoot _) * (_ * digitPhase binaryRoot _)
  have h := @endpoints_normalization 1 1 1 k rfl
  simp only [pow_one, Nat.mul_one] at h
  unfold character
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  rw [← h]
  ring

section Common
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {T : Type*} [DecidableEq T] {D f : ℕ} (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)

/-- Pull back the axis characters through a pair of dual coordinate charts. -/
theorem axes_of_pairing (p q : V → Fin D → ZMod 2)
    (hB : ∀ v u, B v u = ∑ d, p v d * q u d) (x y : Fin f → V) :
    (∏ d, axis (fun c => p (x c) d) (fun c => q (y c) d)) =
      ((w : ℂ)^f)^D * character (∑ c, B (x c) (y c)) := by
  simp_rw [axis_character]
  rw [prod_mul_distrib]
  simp only [prod_const, card_univ, Fintype.card_fin]
  congr 1
  unfold character
  rw [← digitPhase_sum]
  simp_rw [hB]
  rw [sum_comm]

/-- Entire common ordinary query, including its spectator test, using two
signs and exactly two families of D normalized axis kernels. -/
theorem common_kernel (p q : V → Fin D → ZMod 2)
    (hB : ∀ v u, B v u = ∑ d, p v d * q u d)
    (i o : PrimeCommonAddress (Fin f) V T) :
    primeCommonKernel binaryRoot B 1 D o i =
      (if i.2 = o.2 then
        character (-(∑ c, B (i.1.1 c) (i.1.2 c))) *
        character (-(∑ c, B (o.1.1 c) (o.1.2 c))) *
        (∏ d, axis (fun c => p (i.1.1 c) d) (fun c => q (o.1.2 c) d)) *
        (∏ d, axis (fun c => p (o.1.1 c) d) (fun c => q (i.1.2 c) d))
      else 0) := by
  classical
  rw [axes_of_pairing B p q hB, axes_of_pairing B p q hB]
  unfold primeCommonKernel
  split_ifs with h <;> try rfl
  simp only [Fintype.card_fin, Units.val_one, inv_one, one_mul, invOf_eq_inv, Nat.cast_ofNat]
  have hs := @endpoints_normalization D D D f (by omega)
  rw [← hs]
  have hd : ∑ c, B (i.1.1 c-o.1.1 c) (o.1.2 c-i.1.2 c) =
      -(∑ c, B (i.1.1 c) (i.1.2 c)) + -(∑ c, B (o.1.1 c) (o.1.2 c)) +
      (∑ c, B (i.1.1 c) (o.1.2 c)) + ∑ c, B (o.1.1 c) (i.1.2 c) := by
    simp only [map_sub, LinearMap.sub_apply, sum_sub_distrib]
    abel
  rw [hd]
  simp only [character, AddChar.map_add_eq_mul]
  ring

end Common
end
end KernelNormalization

end NearSquareRoot
end Computability
end OAI
