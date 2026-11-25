import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping
import OAI.LinearAlgebra.SpectralBooks.SubsetNormalizedPoint
import OAI.LinearAlgebra.SpectralBooks.CutSpectrum

/-! # Normalization of prices along finite placements

Append a scalar leg at each ambient site. The resulting placement is surjective,
so grouping pulls the ambient spectral point back to the enlarged set of sites.
Normalizing on the original sites expresses every placed price in terms of the
price of the placed binary diagonal.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

noncomputable section

variable {I J : Type} {F : Type*} [Fintype I] [Fintype J] [Field F]

/-- Scalar legs appended before grouping contribute one basis choice at each site. -/
theorem Raw.group_withTrivial_equivalent (σ : I → J) (T : Raw.{0} I F) :
    ((T.withTrivial J).group (Sum.elim σ id)).Equivalent (T.group σ) := by
  let e (j : J) : (((T.withTrivial J).group (Sum.elim σ id)).Leg j) ≃ (T.group σ).Leg j :=
    { toFun := fun x i => x ⟨.inl i.val, i.property⟩
      invFun := fun y i => match i with
        | ⟨.inl k, h⟩ => y ⟨k, h⟩
        | ⟨.inr _, _⟩ => PUnit.unit
      left_inv := by
        intro x
        funext i
        rcases i with ⟨k | k, h⟩ <;> rfl
      right_inv := fun _ => rfl }
  exact Raw.reindex_equivalent e (fun _ => rfl)

variable [Nontrivial I] [Nonempty J]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J F → _ → Prop))

/-- Restricting the price to a finite placement gives a single normalized point
on the original sites, scaled by the price of the placed binary diagonal. -/
theorem rawLogPrice_group_placement (σ : I → J) (c : ℝ) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I F → _ → Prop),
      ∀ T : Raw.{0} I F, rawLogPrice φ c (T.group σ) =
        rawLogPrice φ c ((Raw.diagonal I F (Fin 2)).group σ) *
          Real.logb 2 (ψ.val (ofRaw T) : ℝ) := by
  let f : I ⊕ J → J := Sum.elim σ id
  have hf : Function.Surjective f := fun j => ⟨Sum.inr j, rfl⟩
  let χ := groupSpectralPoint f hf φ
  have eval (T : Raw.{0} I F) :
      χ.val (withTrivialHom J (ofRaw T)) = φ.val (ofRaw (T.group σ)) :=
    congrArg φ.val (ofRaw_eq_iff.mpr (Raw.group_withTrivial_equivalent σ T))
  have hd : c * subsetDiagonalExponent χ =
      rawLogPrice φ c ((Raw.diagonal I F (Fin 2)).group σ) :=
    congrArg (fun z : NNReal => c * Real.logb 2 (z : ℝ)) (eval (Raw.diagonal I F (Fin 2)))
  have hp : 0 ≤ subsetDiagonalExponent χ := by
    simpa only [rawLogPrice, one_mul, subsetDiagonalExponent] using
      rawLogPrice_nonneg χ (c := 1) (by norm_num) (Raw.supportDiagonal I J F (Fin 2))
  rcases hp.eq_or_lt with hz | hpos
  · obtain ⟨ψ, hψ⟩ := spectrum_nonempty I F
    refine ⟨⟨ψ, hψ⟩, fun T => ?_⟩
    rw [← hd, ← hz, mul_zero, zero_mul, rawLogPrice, ← eval]
    rw [subset_log_price_eq_zero_of_diagonal χ hz.symm, mul_zero]
  · refine ⟨normalizedSubsetPoint χ hpos, fun T => ?_⟩
    rw [← hd, rawLogPrice, ← eval]
    exact normalizedSubsetPoint_price χ hpos (ofRaw T) c

/-- The normalization formula for an embedded finite set of sites. -/
theorem rawLogPrice_group_embedding (e : I ↪ J) (c : ℝ) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I F → _ → Prop),
      ∀ T : Raw.{0} I F, rawLogPrice φ c (T.group e) =
        rawLogPrice φ c ((Raw.diagonal I F (Fin 2)).group e) *
          Real.logb 2 (ψ.val (ofRaw T) : ℝ) :=
  rawLogPrice_group_placement φ e c

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
