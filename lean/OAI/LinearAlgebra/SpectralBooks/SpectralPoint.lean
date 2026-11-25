import OAI.LinearAlgebra.SpectralBooks.Tensor
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Spectral evaluation and tensor rank

We record the properties of a normalized spectral point needed for a rank lower
bound. All local maps act on actual three-site coefficient tensors. The
comparison with asymptotic rank follows by applying the exact rank comparison
to every positive tensor power.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped NNReal

section

/-- The normalized, multiplicative, restriction-monotone evaluation underlying a
three-site spectral point. Only its laws used in the rank comparison are required. -/
structure RankFunctional (F : Type*) [Field F] where
  value {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] : Tensor F X Y Z → ℝ≥0
  diagonal (r : ℕ) : value (Tensor.diagonal (K := F) (Fin r)) = r
  product {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
      [Fintype U] [Fintype V] [Fintype W] (T : Tensor F X Y Z) (S : Tensor F U V W) :
    value (Tensor.product T S) = value T * value S
  restrict_le {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
      [Fintype U] [Fintype V] [Fintype W] (T : Tensor F X Y Z)
      (A : U → X → F) (B : V → Y → F) (C : W → Z → F) :
    value (Tensor.restrict A B C T) ≤ value T

namespace RankFunctional

variable {F : Type*} [Field F] (φ : RankFunctional F)
variable {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype U] [Fintype V] [Fintype W]

theorem pullback_le (T : Tensor F X Y Z) (a : U → X) (b : V → Y) (c : W → Z) :
    φ.value (Tensor.pullback a b c T) ≤ φ.value T := by
  classical
  convert φ.restrict_le T
      (fun u x => if x = a u then 1 else 0)
      (fun v y => if y = b v then 1 else 0)
      (fun w z => if z = c w then 1 else 0) using 2
  funext u v w
  simp [Tensor.pullback, Tensor.restrict, ite_mul, mul_ite]

theorem pullback_equiv (T : Tensor F X Y Z) (a : U ≃ X) (b : V ≃ Y) (c : W ≃ Z) :
    φ.value (Tensor.pullback a b c T) = φ.value T := by
  refine le_antisymm (φ.pullback_le T a b c) ?_
  have h := φ.pullback_le (Tensor.pullback a b c T) a.symm b.symm c.symm
  have heq : Tensor.pullback a.symm b.symm c.symm (Tensor.pullback a b c T) = T := by
    funext x y z
    simp [Tensor.pullback]
  rwa [heq] at h

theorem le_of_rankAtMost {T : Tensor F X Y Z} {r : ℕ} (hr : Tensor.RankAtMost T r) :
    φ.value T ≤ r := by
  obtain ⟨a,b,c,ht⟩ := hr
  have heq : Tensor.restrict (fun x i => a i x) (fun y j => b j y)
      (fun z k => c k z) (Tensor.diagonal (K := F) (Fin r)) = T := by
    rw [ht]
    funext x y z
    simp [Tensor.restrict, Tensor.diagonal, Tensor.rankOne, mul_ite, ite_and]
  rw [← φ.diagonal, ← heq]
  apply φ.restrict_le

theorem le_tensorRank (T : Tensor F X Y Z) : φ.value T ≤ tensorRank T :=
  φ.le_of_rankAtMost (rankAtMost_tensorRank T)

/-- An entry equal to one supplies the one-dimensional unit tensor. -/
theorem one_le_of_entry_one {T : Tensor F X Y Z} {x : X} {y : Y} {z : Z}
    (h : T x y z = 1) : 1 ≤ φ.value T := by
  have heq : Tensor.pullback (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) (fun _ : Fin 1 => z) T =
      Tensor.diagonal (K := F) (Fin 1) := by
    funext i j k
    simp [Tensor.pullback, Tensor.diagonal, h, Subsingleton.elim i j, Subsingleton.elim j k]
  have hh := φ.pullback_le T (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) (fun _ : Fin 1 => z)
  simpa only [heq, φ.diagonal, Nat.cast_one] using hh

private def uncons {A : Type} (n : ℕ) : (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0, fun i => f i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv f := by funext i; induction i using Fin.cases <;> simp
  right_inv x := by ext <;> simp

theorem power_succ (T : Tensor F X Y Z) (n : ℕ) :
    φ.value (Tensor.power T (n + 1)) = φ.value T ^ (n + 1) := by
  induction n with
  | zero =>
    let e (A : Type) : (Fin 1 → A) ≃ A := Equiv.funUnique (Fin 1) A
    have ht : Tensor.power T 1 = Tensor.pullback (e X) (e Y) (e Z) T := by
      funext x y z
      simp [Tensor.power, Tensor.pullback, e, Equiv.funUnique, Subsingleton.elim (default : Fin 1) 0]
    rw [ht, φ.pullback_equiv, pow_one]
  | succ n ih =>
    have ht : Tensor.power T (n + 1 + 1) =
        Tensor.pullback (uncons (n + 1)) (uncons (n + 1)) (uncons (n + 1))
          (Tensor.product T (Tensor.power T (n + 1))) := by
      funext x y z
      exact Fin.prod_univ_succ _
    rw [ht, φ.pullback_equiv, φ.product, ih, pow_succ' _ (n + 1)]

/-- A normalized spectral evaluation is bounded by the infimum of the
positive power rank roots, in the ground field. -/
theorem le_asymptoticRank (T : Tensor F X Y Z) : (φ.value T : ℝ) ≤ asymptoticRank T := by
  apply le_ciInf
  intro n
  have h := φ.le_tensorRank (Tensor.power T (n + 1))
  rw [φ.power_succ] at h
  have hr : (φ.value T : ℝ) ^ (n + 1) ≤ tensorRank (Tensor.power T (n + 1)) := by
    exact_mod_cast h
  have hroot := Real.rpow_le_rpow (by positivity) hr (by positivity : 0 ≤ ((n + 1 : ℝ)⁻¹))
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), Nat.cast_succ,
    mul_inv_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), Real.rpow_one] at hroot

end RankFunctional
end

end

end SpectralBooks
end LinearAlgebra
end OAI
