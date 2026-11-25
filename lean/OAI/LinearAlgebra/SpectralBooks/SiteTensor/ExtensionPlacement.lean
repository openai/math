import OAI.LinearAlgebra.SpectralBooks.OldSiteEmbedding
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose
import OAI.LinearAlgebra.SpectralBooks.RawLogPrice

/-! # Old placements after adjoining a site

Grouping along the inclusion of the old sites contributes an empty product of
coordinate bases at the new site. This scalar factor realizes the old tensor
embedding, including when several slots occupy the same old site.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v
variable {A I : Type} {K : Type*} [Fintype A] [Fintype I] [CommSemiring K]

private def groupSomeLegEquiv (T : Raw.{v} I K) (j : Option I) :
    (T.group some).Leg j ≃ T.embedOld.Leg j := by
  cases j with
  | none =>
    exact ⟨fun _ => PUnit.unit, fun _ t => (nomatch t.property),
      fun _ => funext fun t => (nomatch t.property), fun _ => rfl⟩
  | some i =>
    exact ⟨fun x => x ⟨i, rfl⟩,
      fun x t => (Option.some.inj t.property).symm ▸ x,
      fun x => by
        funext ⟨k, hk⟩
        cases Option.some.inj hk
        rfl,
      fun _ => rfl⟩

/-- The tensor with a trivial new slot is the old tensor placed by inclusion. -/
theorem ofRaw_embedOld_eq_group_some (T : Raw.{v} I K) :
    ofRaw T.embedOld = ofRaw (T.group some) := by
  symm
  exact ofRaw_eq_iff.mpr (Raw.reindex_equivalent (groupSomeLegEquiv T) (fun _ => rfl))

/-- Any placement using the old sites agrees with its composite with the inclusion. -/
theorem ofRaw_embedOld_group (T : Raw.{v} A K) (σ : A → I) :
    ofRaw (T.group σ).embedOld = ofRaw (T.group (some ∘ σ)) :=
  (ofRaw_embedOld_eq_group_some _).trans (ofRaw_eq_iff.mpr (Raw.group_group_equivalent T σ some))

section Prices

variable {F : Type*} [Field F] [Nonempty I]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I F → _ → Prop))
variable (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} (Option I) F → _ → Prop))

/-- Agreement on the nonzero old tensors gives agreement for all their placements,
including zero tensors, at the respective price scales. -/
theorem rawLogPrice_group_some_comp (c d : ℝ)
    (h : ∀ X : Raw.{v} I F, X.coeff ≠ 0 →
      rawLogPrice ψ d X.embedOld = rawLogPrice φ c X)
    (T : Raw.{v} A F) (σ : A → I) :
    rawLogPrice ψ d (T.group (some ∘ σ)) = rawLogPrice φ c (T.group σ) := by
  by_cases hT : T.coeff = 0
  · have hzero {J : Type} (p : A → J) : (T.group p).coeff = 0 :=
      funext fun x => congrFun hT _
    rw [rawLogPrice_zero ψ _ _ (hzero _), rawLogPrice_zero φ _ _ (hzero _)]
  · have he := h (T.group σ) ((T.group_ne_zero_iff σ).mpr hT)
    simpa only [rawLogPrice, ofRaw_embedOld_group] using he

end Prices
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
