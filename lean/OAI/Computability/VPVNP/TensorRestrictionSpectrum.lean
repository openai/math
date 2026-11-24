import OAI.Computability.VPVNP.TensorRestrictionSemiring
import OAI.Computability.VPVNP.WireSpectrum

/-!
# Spectral points on the semiring of tensor restriction classes

A spectral point is constant on each class of mutually restricting tensors.
Its real values define a monotone semiring homomorphism on the quotient.
Conversely, monotonicity bounds the values of such a homomorphism below by
zero, so its evaluations on tensor representatives form a spectral point.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v
open scoped NNReal

namespace WireTensor.RestrictionClass

variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nonempty J]

/-- Real-valued evaluation of a spectral point on restriction classes. -/
noncomputable def ofSpectralPoint (F : SpectralPoint k J) : RestrictionClass k J →+* ℝ where
  toFun := Quotient.lift (fun T ↦ (F.value T : ℝ))
    (fun _ _ h ↦ congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) (F.value_eq_of_mutual h))
  map_zero' := by
    change (F.value (diagonal (Fin 0)) : ℝ) = 0
    simp [F.value_diagonal_fin]
  map_one' := by
    change (F.value unit : ℝ) = 1
    simp [F.value_unit]
  map_add' a b := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective a
    obtain ⟨U, rfl⟩ := ofTensor_surjective b
    change (F.value (directSum T U) : ℝ) = (F.value T : ℝ) + F.value U
    rw [F.value_directSum, NNReal.coe_add]
  map_mul' a b := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective a
    obtain ⟨U, rfl⟩ := ofTensor_surjective b
    change (F.value (tensorProduct T U) : ℝ) = (F.value T : ℝ) * F.value U
    rw [F.value_tensorProduct, NNReal.coe_mul]

@[simp] theorem ofSpectralPoint_ofTensor (F : SpectralPoint k J) (T : Tensor.{u,v,0} k J) :
    ofSpectralPoint F (ofTensor T) = (F.value T : ℝ) := rfl

theorem ofSpectralPoint_monotone (F : SpectralPoint k J) : Monotone (ofSpectralPoint F) := by
  intro a b hab
  obtain ⟨T, rfl⟩ := ofTensor_surjective a
  obtain ⟨U, rfl⟩ := ofTensor_surjective b
  exact F.monotone ((ofTensor_le_iff T U).1 hab)

/-- Evaluate a monotone real-valued semiring homomorphism on tensor representatives. -/
noncomputable def toSpectralPoint (f : RestrictionClass k J →+* ℝ) (hf : Monotone f) :
    SpectralPoint k J where
  value T := ⟨f (ofTensor T), by simpa using hf (orderBounds.zero_le (ofTensor T))⟩
  monotone h := hf ((ofTensor_le_iff _ _).2 h)
  value_unit := NNReal.eq f.map_one
  value_zero T hT := NNReal.eq (show f (ofTensor T) = 0 by rw [(ofTensor_eq_zero_iff T).2 hT, map_zero])
  value_directSum T U := NNReal.eq (f.map_add (ofTensor T) (ofTensor U))
  value_tensorProduct T U := NNReal.eq (f.map_mul (ofTensor T) (ofTensor U))

@[simp] theorem coe_toSpectralPoint_value (f : RestrictionClass k J →+* ℝ) (hf : Monotone f)
    (T : Tensor.{u,v,0} k J) : ((toSpectralPoint f hf).value T : ℝ) = f (ofTensor T) := rfl

/-- The two descriptions of the tensor spectrum agree point by point. -/
noncomputable def spectralPointEquiv :
    SpectralPoint k J ≃ {f : RestrictionClass k J →+* ℝ // Monotone f} where
  toFun F := ⟨ofSpectralPoint F, ofSpectralPoint_monotone F⟩
  invFun f := toSpectralPoint f.val f.property
  left_inv _ := rfl
  right_inv f := by
    apply Subtype.ext
    apply RingHom.ext
    intro a
    obtain ⟨T, rfl⟩ := ofTensor_surjective a
    rfl

/-- One spectral point distinguishes every pair of distinct natural-number classes. -/
theorem charZeroOfSpectralPoint (F : SpectralPoint k J) : CharZero (RestrictionClass k J) :=
  (ofSpectralPoint F).charZero

end WireTensor.RestrictionClass

end VPVNP
end Computability
end OAI
