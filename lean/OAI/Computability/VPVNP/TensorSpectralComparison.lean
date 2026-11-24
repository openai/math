import OAI.Computability.VPVNP.StarEmbedding
import OAI.Computability.VPVNP.TensorFlatteningPoint
import OAI.Computability.VPVNP.TensorRestrictionSpectrum
import OAI.Computability.VPVNP.SpectralStrictComparison

/-!
# Strict spectral comparison for tensor restrictions

Lemma 2.1 turns strict comparison at all spectral points into local linear
maps on every tensor power. The same number of copies of the supply tensor
works for every power. A flattening at a single party supplies the required
natural-valued rank on mutual-restriction classes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

open RestrictionClass

universe u v

variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nontrivial J]

/-- One integer copy bound gives genuine local linear restrictions for all
powers, whenever all spectral points strictly prefer the supply tensor. -/
theorem tensor_strict_spectral_comparison
    {X Y : Tensor.{u,v,0} k J} (hY : Y.coeff ≠ 0)
    (h : ∀ F : SpectralPoint k J, F.value X < F.value Y) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ m : ℕ,
      Restricts (tensorProduct (diagonal (Fin K)) (tensorPowerFin m Y)) (tensorPowerFin m X) := by
  let a := Classical.choice (inferInstance : Nonempty J)
  let rank := flatteningRankHom (k := k) a
  let : CharZero (RestrictionClass k J) := rank.charZero
  have h' (F : RestrictionClass k J →+* ℝ) (hF : Monotone F) : F (ofTensor X) < F (ofTensor Y) :=
    h (toSpectralPoint F hF)
  obtain ⟨K, hK, hpow⟩ := Spectral.strict_spectral_comparison orderBounds rank (flatteningRankHom_monotone a)
    (fun hy => hY ((ofTensor_eq_zero_iff Y).mp hy)) h'
  refine ⟨K, hK, fun m => (ofTensor_le_iff _ _).mp ?_⟩
  simpa only [ofTensor_tensorProduct, ofTensor_diagonal_fin, ofTensor_tensorPowerFin] using hpow m

end WireTensor

end VPVNP
end Computability
end OAI
