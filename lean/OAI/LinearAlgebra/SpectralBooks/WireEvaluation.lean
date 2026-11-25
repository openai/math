import OAI.LinearAlgebra.SpectralBooks.DimensionLaw
import OAI.LinearAlgebra.SpectralBooks.SpectralPoint
import OAI.LinearAlgebra.SpectralBooks.WireProduct

/-! # The price of each matrix multiplication wire

A normalized spectral evaluation on three sites gives a monotone multiplicative
function of the dimension on each of the three wires. Hence its logarithmic
wire price is its binary wire price times the logarithm of the dimension.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open MatrixMultiplication.Foundation
open scoped NNReal
namespace RankFunctional

variable {F : Type*} [Field F] (φ : RankFunctional F)

/-- The normalized values of the three wires in cyclic order. -/
def wireValue (e : Fin 3) (n : ℕ) : ℝ≥0 :=
  ![φ.value (wire12 F n), φ.value (wire23 F n), φ.value (wire31 F n)] e

theorem wireValue_mono (e : Fin 3) : Monotone (φ.wireValue e) := by
  intro m n h
  let f := Fin.castLE h
  have hf : Function.Injective f := Fin.castLE_injective h
  fin_cases e
  · have hp : Tensor.pullback f f id (wire12 F n) = wire12 F m := by
      funext i j k
      simp [Tensor.pullback, wire12, hf.eq_iff]
    change φ.value (wire12 F m) ≤ _
    rw [← hp]
    exact φ.pullback_le _ _ _ _
  · have hp : Tensor.pullback id f f (wire23 F n) = wire23 F m := by
      funext i j k
      simp [Tensor.pullback, wire23, hf.eq_iff]
    change φ.value (wire23 F m) ≤ _
    rw [← hp]
    exact φ.pullback_le _ _ _ _
  · have hp : Tensor.pullback f id f (wire31 F n) = wire31 F m := by
      funext i j k
      simp [Tensor.pullback, wire31, hf.eq_iff]
    change φ.value (wire31 F m) ≤ _
    rw [← hp]
    exact φ.pullback_le _ _ _ _

theorem wireValue_one (e : Fin 3) : φ.wireValue e 1 = 1 := by
  let f : Unit ≃ Fin 1 := Equiv.ofUnique _ _
  let D := Tensor.diagonal (K := F) (Fin 1)
  fin_cases e
  · have hp : Tensor.pullback (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1)) f D = wire12 F 1 := by
      funext i j k
      have heq : ∀ u v : Fin 1, u = v := fun _ _ => Subsingleton.elim _ _
      simp [Tensor.pullback, wire12, D, Tensor.diagonal]
      grind
    change φ.value (wire12 F 1) = 1
    rw [← hp, φ.pullback_equiv, φ.diagonal, Nat.cast_one]
  · have hp : Tensor.pullback f (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1)) D = wire23 F 1 := by
      funext i j k
      have heq : ∀ u v : Fin 1, u = v := fun _ _ => Subsingleton.elim _ _
      simp [Tensor.pullback, wire23, D, Tensor.diagonal]
      grind
    change φ.value (wire23 F 1) = 1
    rw [← hp, φ.pullback_equiv, φ.diagonal, Nat.cast_one]
  · have hp : Tensor.pullback (Equiv.refl (Fin 1)) f (Equiv.refl (Fin 1)) D = wire31 F 1 := by
      funext i j k
      have heq : ∀ u v : Fin 1, u = v := fun _ _ => Subsingleton.elim _ _
      simp [Tensor.pullback, wire31, D, Tensor.diagonal]
      grind
    change φ.value (wire31 F 1) = 1
    rw [← hp, φ.pullback_equiv, φ.diagonal, Nat.cast_one]

theorem wireValue_mul (e : Fin 3) (m n : ℕ) :
    φ.wireValue e (m * n) = φ.wireValue e m * φ.wireValue e n := by
  let f : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  let u : Unit × Unit ≃ Unit := Equiv.prodUnique Unit Unit
  fin_cases e
  · have hp : Tensor.pullback f f u (wire12 F (m * n)) =
        Tensor.product (wire12 F m) (wire12 F n) := by
      funext i j k
      simp [Tensor.pullback, Tensor.product, wire12, Prod.ext_iff, ite_and, mul_ite]
      grind
    change φ.value (wire12 F (m * n)) = φ.value (wire12 F m) * φ.value (wire12 F n)
    rw [← φ.product, ← hp, φ.pullback_equiv]
  · have hp : Tensor.pullback u f f (wire23 F (m * n)) =
        Tensor.product (wire23 F m) (wire23 F n) := by
      funext i j k
      simp [Tensor.pullback, Tensor.product, wire23, Prod.ext_iff, ite_and, mul_ite]
      grind
    change φ.value (wire23 F (m * n)) = φ.value (wire23 F m) * φ.value (wire23 F n)
    rw [← φ.product, ← hp, φ.pullback_equiv]
  · have hp : Tensor.pullback f u f (wire31 F (m * n)) =
        Tensor.product (wire31 F m) (wire31 F n) := by
      funext i j k
      simp [Tensor.pullback, Tensor.product, wire31, Prod.ext_iff, ite_and, mul_ite]
      grind
    change φ.value (wire31 F (m * n)) = φ.value (wire31 F m) * φ.value (wire31 F n)
    rw [← φ.product, ← hp, φ.pullback_equiv]

/-- The value of a wire of arbitrary positive order is determined by its
binary value at the same placement. -/
theorem wireValue_eq_rpow (e : Fin 3) {n : ℕ} (hn : 0 < n) :
    (φ.wireValue e n : ℝ) = (n : ℝ) ^ Real.logb 2 (φ.wireValue e 2) := by
  exact dimension_value_eq_rpow (v := fun q => (φ.wireValue e q : ℝ))
    (fun _ _ hij => by exact_mod_cast φ.wireValue_mono e hij)
    (by simp [φ.wireValue_one]) (fun m q => by simp [φ.wireValue_mul]) hn

/-- Formula for the logarithmic price of a wire on any of the three edges. -/
theorem logb_wireValue (e : Fin 3) {n : ℕ} (hn : 0 < n) :
    Real.logb 2 (φ.wireValue e n) = Real.logb 2 (φ.wireValue e 2) * Real.logb 2 n := by
  rw [φ.wireValue_eq_rpow e hn, Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]

end RankFunctional

end

end SpectralBooks
end LinearAlgebra
end OAI
