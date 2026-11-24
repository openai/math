import OAI.Computability.VPVNP.WireSpectrum

/-!
# Compactness of the tensor spectrum

Section 2 of *VP and VNP differ over every field* uses the topology of
pointwise convergence on spectral points. Their defining equations and
restriction inequalities cut out a closed subset of a product of compact
intervals. The upper endpoints are the coordinate rank bounds.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v

open scoped NNReal
open Set

namespace WireTensor.SpectralPoint

variable {k : Type u} {J : Type v} [Field k] [Fintype J]

/-- The defining conditions of spectral points are closed under pointwise limits. -/
theorem isClosed_range_value : IsClosed (range (value (k := k) (J := J))) := by
  let A := Tensor.{u,v,0} k J
  have hrange : range (value (k := k) (J := J)) =
      {f : A → ℝ≥0 | (∀ Y X, Restricts Y X → f X ≤ f Y) ∧ f unit = 1 ∧
        (∀ T, T.coeff = 0 → f T = 0) ∧
        (∀ T U, f (directSum T U) = f T + f U) ∧
        (∀ T U, f (tensorProduct T U) = f T * f U)} := by
    ext f
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨fun _ _ h ↦ F.monotone h, F.value_unit, F.value_zero,
        F.value_directSum, F.value_tensorProduct⟩
    · rintro ⟨hm, hu, hz, hs, hp⟩
      exact ⟨⟨f, fun {Y X} ↦ hm Y X, hu, hz, hs, hp⟩, rfl⟩
  rw [hrange]
  simp only [ofPred_and, ofPred_forall]
  refine (isClosed_iInter fun Y ↦ isClosed_iInter fun X ↦ isClosed_iInter fun _ ↦
    isClosed_le (continuous_apply X) (continuous_apply Y)).inter ?_
  refine (isClosed_eq (continuous_apply unit) continuous_const).inter ?_
  refine (isClosed_iInter fun T ↦ isClosed_iInter fun _ ↦
    isClosed_eq (continuous_apply T) continuous_const).inter ?_
  exact (isClosed_iInter fun T ↦ isClosed_iInter fun U ↦ isClosed_eq
    (continuous_apply (directSum T U)) ((continuous_apply T).add (continuous_apply U))).inter
    (isClosed_iInter fun T ↦ isClosed_iInter fun U ↦ isClosed_eq
      (continuous_apply (tensorProduct T U)) ((continuous_apply T).mul (continuous_apply U)))

/-- The spectrum of tensors on a finite nonempty party set is compact for the
topology of pointwise convergence. -/
theorem isCompact_range_value [Nonempty J] : IsCompact (range (value (k := k) (J := J))) := by
  let bound (T : Tensor.{u,v,0} k J) : ℝ≥0 := ↑(∏ j, Fintype.card (T.Basis j) : ℕ)
  have hc := isCompact_pi_infinite (fun T ↦ isCompact_Icc (a := (0 : ℝ≥0)) (b := bound T))
  apply hc.of_isClosed_subset isClosed_range_value
  rintro _ ⟨F, rfl⟩ T
  exact ⟨zero_le, F.value_le_basis_product T⟩

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
