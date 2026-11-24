import OAI.Computability.VPVNP.ContractionValue
import OAI.Computability.VPVNP.StarEmbedding
import OAI.Computability.VPVNP.TensorRestrictionSpectrum

/-!
# Center contractions on restriction classes

The supremal contraction value descends to the extended-party restriction
classes. Its additivity evaluates the copy multiplicities on both sides of
the comparison in Theorem 2.4. Multiplication by an embedded old tensor
can also be evaluated, even with an arbitrary covector on the other factor.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v
open scoped NNReal

namespace WireTensor.SpectralPoint

open RestrictionClass

variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nonempty J] (F : SpectralPoint k J)

/-- Real-valued supremal contraction on classes, preserving finite direct sums. -/
noncomputable def contractionClassValue : RestrictionClass k (Option J) →+ ℝ where
  toFun := Quotient.lift (fun T ↦ (F.contractionValue T : ℝ)) (fun _ _ h ↦
    congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) (le_antisymm (F.contractionValue_mono h.2)
      (F.contractionValue_mono h.1)))
  map_zero' := by
    change (F.contractionValue (diagonal (Fin 0)) : ℝ) = 0
    rw [F.contractionValue_zero]
    · rfl
    · funext x
      exact Fin.elim0 (x none)
  map_add' x y := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective x
    obtain ⟨U, rfl⟩ := ofTensor_surjective y
    change (F.contractionValue (directSum T U) : ℝ) = F.contractionValue T + F.contractionValue U
    rw [F.contractionValue_directSum, NNReal.coe_add]

@[simp] theorem contractionClassValue_ofTensor (T : Tensor.{u,v,0} k (Option J)) :
    F.contractionClassValue (ofTensor T) = (F.contractionValue T : ℝ) := rfl

theorem contractionClassValue_monotone : Monotone F.contractionClassValue := by
  intro x y h
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  obtain ⟨U, rfl⟩ := ofTensor_surjective y
  exact NNReal.coe_le_coe.mpr (F.contractionValue_mono ((ofTensor_le_iff T U).mp h))

@[simp] theorem contractionClassValue_one : F.contractionClassValue 1 = 1 := by
  change (F.contractionValue unit : ℝ) = 1
  rw [F.contractionValue_unit, NNReal.coe_one]

theorem contractionClassValue_nonneg (x : RestrictionClass k (Option J)) :
    0 ≤ F.contractionClassValue x := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  exact NNReal.coe_nonneg _

theorem one_le_contractionClassValue {x : RestrictionClass k (Option J)} (hx : x ≠ 0) :
    1 ≤ F.contractionClassValue x := by
  rw [← F.contractionClassValue_one]
  exact F.contractionClassValue_monotone (orderBounds.one_le hx)

/-- A natural-number copy factor gives that many times the single value. -/
@[simp] theorem contractionClassValue_copies (n : ℕ) (x : RestrictionClass k (Option J)) :
    F.contractionClassValue ((n : RestrictionClass k (Option J)) * x) = n * F.contractionClassValue x := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

/-- Evaluating a class with an embedded old factor leaves only the
contraction value of the remaining extended-party class. -/
theorem contractionClassValue_old_product (x : RestrictionClass k J) (y : RestrictionClass k (Option J)) :
    F.contractionClassValue (embedOldClass x * y) = ofSpectralPoint F x * F.contractionClassValue y := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  obtain ⟨U, rfl⟩ := ofTensor_surjective y
  rw [embedOldClass_ofTensor, ← ofTensor_tensorProduct, contractionClassValue_ofTensor,
    F.contractionValue_old_product, NNReal.coe_mul, contractionClassValue_ofTensor, ofSpectralPoint_ofTensor]

/-- A center leg of dimension one preserves the old spectral point on classes. -/
@[simp] theorem contractionClassValue_embedOldClass (x : RestrictionClass k J) :
    F.contractionClassValue (embedOldClass x) = ofSpectralPoint F x := by
  simpa only [mul_one, F.contractionClassValue_one] using F.contractionClassValue_old_product x 1

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
