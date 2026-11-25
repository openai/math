import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping
import OAI.LinearAlgebra.SpectralBooks.StretchClassPrice

/-! # Pulling a price back to the indices of a placement

A placement can list the same metric point many times. Factor it through the
finite set of occupied points. On that set the injective placement supplies
a normalized spectral point; grouping along the surjection pulls this point
back to the original tensor semiring.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SpectralPlacementPrices

open SiteTensor

variable {I : Type} [Fintype I] [Nonempty I] {X K : Type*} [MetricSpace X] [Field K]

/-- All tensors placed according to a fixed list are priced by a single
spectral price on the original finite set of indices. The list may have
repetitions, and a constant list yields the zero price. -/
theorem exists_spectralPrice_of_placement (P : SpectralPlacementPrices K X) (σ : I → X) :
    ∃ g : NonzeroProduct.{0} I K →+ ℝ, IsSpectralPrice unit_le_nonzeroClass g ∧
      ∀ T : Raw.{0} I K, P.price T σ = classPrice g (ofRaw T) := by
  classical
  let A := Set.range σ
  let : Fintype A := Fintype.ofFinite A
  let J := Fin (Fintype.card A)
  let e : A ≃ J := Fintype.equivFin A
  let v : J ↪ X := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  let q : I → J := e ∘ Set.rangeFactorization σ
  have hq : Function.Surjective q := e.surjective.comp Set.rangeFactorization_surjective
  have hvq : v ∘ q = σ := funext fun i => congrArg Subtype.val (e.symm_apply_apply _)
  let : Nonempty J := ⟨q (Classical.arbitrary I)⟩
  rcases subsingleton_or_nontrivial J with hJ | hJ
  · let i := Classical.arbitrary I
    have hs : σ = fun _ => σ i := by
      rw [← hvq]
      exact funext fun j => congrArg v (Subsingleton.elim (q j) (q i))
    refine ⟨0, Or.inl rfl, fun T => ?_⟩
    exact (congrArg (P.price T) hs).trans <|
      (P.collapsed T (σ i)).trans (classPrice_zero _).symm
  · obtain ⟨φ, hpos, hφ⟩ := P.normalized_group v
    let ψ := groupSpectralPoint q hq φ
    let d := P.price (Raw.diagonal J K (Fin 2)) v
    refine ⟨d • logPoint ψ, Or.inr ⟨ψ, d, hpos, rfl⟩, fun T => ?_⟩
    by_cases hT : T.coeff = 0
    · rw [P.zero_tensor T hT σ, (ofRaw_eq_zero_iff T).mpr hT]
      simp [classPrice]
    rw [← hvq, hφ q T hT, classPrice_scaled_log]
    rfl

end SpectralPlacementPrices

end SpectralBooks
end LinearAlgebra
end OAI
