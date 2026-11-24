import OAI.Computability.VPVNP.FlatteningKronecker
import OAI.Computability.VPVNP.TensorFlatteningSum
import OAI.Computability.VPVNP.TensorRestrictionSpectrum

/-!
# Flattening rank as a tensor spectral point

For a party set with at least two elements, separating any one party
from the rest gives an additive, multiplicative, restriction-monotone rank.
Appendix A.1 uses this natural-valued homomorphism on restriction classes
to exclude the negative order unit from the comparison cone.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

namespace WireTensor

universe u v
variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nontrivial J]

/-- The matrix rank across a single-party cut, on mutual restriction classes. -/
noncomputable def flatteningRankHom (a : J) : RestrictionClass k J →+* ℕ where
  toFun := Quotient.lift (fun T => (flattening a T).rank)
    (fun _ _ h => le_antisymm (flattening_rank_mono a h.2) (flattening_rank_mono a h.1))
  map_zero' := by
    change (flattening a (diagonal (k := k) (Fin 0))).rank = 0
    apply flattening_zero_rank
    funext x
    exact (x a).elim0
  map_one' := flattening_unit_rank a
  map_add' x y := by
    obtain ⟨T, rfl⟩ := RestrictionClass.ofTensor_surjective x
    obtain ⟨U, rfl⟩ := RestrictionClass.ofTensor_surjective y
    exact flattening_directSum_rank a T U
  map_mul' x y := by
    obtain ⟨T, rfl⟩ := RestrictionClass.ofTensor_surjective x
    obtain ⟨U, rfl⟩ := RestrictionClass.ofTensor_surjective y
    exact (flattening_product_rank a T U).trans (rank_kronecker _ _)

@[simp] theorem flatteningRankHom_ofTensor (a : J) (T : Tensor.{u,v,0} k J) :
    flatteningRankHom a (RestrictionClass.ofTensor T) = (flattening a T).rank := rfl

theorem flatteningRankHom_monotone (a : J) : Monotone (flatteningRankHom (k := k) a) := by
  intro x y h
  obtain ⟨T, rfl⟩ := RestrictionClass.ofTensor_surjective x
  obtain ⟨U, rfl⟩ := RestrictionClass.ofTensor_surjective y
  exact flattening_rank_mono a ((RestrictionClass.ofTensor_le_iff T U).1 h)

/-- The spectral point measuring the rank across the chosen cut. -/
noncomputable def flatteningPoint (a : J) : SpectralPoint k J :=
  RestrictionClass.toSpectralPoint ((Nat.castRingHom ℝ).comp (flatteningRankHom a))
    (fun _ _ h => Nat.cast_le.mpr (flatteningRankHom_monotone a h))

@[simp] theorem coe_flatteningPoint_value (a : J) (T : Tensor.{u,v,0} k J) :
    ((flatteningPoint a).value T : ℝ) = (flattening a T).rank := rfl

end WireTensor

end VPVNP
end Computability
end OAI
