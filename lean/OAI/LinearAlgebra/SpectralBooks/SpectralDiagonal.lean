import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nonzero

/-! # The binary diagonal price on occupied sites

A finite site set is enumerated by `Fin S.card` to allow arbitrary ambient
universes. Grouping repeated labels onto their occupied sites preserves its
binary diagonal class because surjective grouping is a semiring homomorphism.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace SpectralPlacementPrices

open SiteTensor

variable {K X : Type*} [Field K] [PseudoMetricSpace X] (P : SpectralPlacementPrices K X)

/-- The binary diagonal price of the finite set of occupied sites, extended by zero
on the empty set. -/
def diagonal (S : Finset X) : ℝ :=
  if S.Nonempty then P.price (Raw.diagonal (Fin S.card) K (Fin 2))
    (fun i ↦ (S.equivFin.symm i).val) else 0

@[simp] theorem diagonal_empty : P.diagonal ∅ = 0 := by simp [diagonal]

/-- On an injective placement equivalent nonzero tensors have equal prices. -/
theorem price_eq_of_class_eq {I : Type} [Fintype I] [Nonempty I] (p : I ↪ X)
    {T V : Raw.{0} I K} (he : ofRaw T = ofRaw V) : P.price T p = P.price V p := by
  cases subsingleton_or_nontrivial I with
  | inl hs =>
    let i : I := Classical.choice inferInstance
    have e : (p : I → X) = fun _ ↦ p i := funext (fun j ↦ congrArg p (Subsingleton.elim j i))
    rw [e, P.collapsed, P.collapsed]
  | inr ht =>
    by_cases hT : T.coeff = 0
    · have hV := (ofRaw_eq_zero_iff V).mp (he.symm.trans ((ofRaw_eq_zero_iff T).mpr hT))
      rw [P.zero_tensor T hT, P.zero_tensor V hV]
    · have hV : V.coeff ≠ 0 := fun h ↦ hT ((ofRaw_eq_zero_iff T).mp
        (he.trans ((ofRaw_eq_zero_iff V).mpr h)))
      obtain ⟨φ, hφ⟩ := P.normalized p
      rw [hφ T hT, hφ V hV, he]

/-- The price of the binary full diagonal on any nonempty list of labels
depends only on the occupied set. This includes all collisions. -/
theorem price_binaryDiagonal_eq {I : Type} [Fintype I] [Nonempty I] (p : I → X) :
    P.price (Raw.diagonal I K (Fin 2)) p = P.diagonal (Finset.univ.image p) := by
  let S := Finset.univ.image p
  have hS : S.Nonempty := Finset.univ_nonempty.image p
  let x : Fin S.card ↪ X := S.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  let σ (i : I) := S.equivFin ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i)⟩
  have hσ : Function.Surjective σ := by
    intro j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (S.equivFin.symm j).property
    refine ⟨i, S.equivFin.symm.injective ?_⟩
    exact Subtype.ext (by simpa only [σ, Equiv.symm_apply_apply] using hi)
  have hp : p = x ∘ σ := funext (fun i ↦ by simp [x, σ])
  have : Nonempty (Fin S.card) := ⟨σ (Classical.choice inferInstance)⟩
  change P.price _ p = P.diagonal S
  rw [diagonal, ite_eq_left hS, hp, P.group]
  apply P.price_eq_of_class_eq x
  change groupClass σ (ofRaw (Raw.diagonal I K (Fin 2))) = _
  rw [ofRaw_diagonal_fin_eq_natCast, ofRaw_diagonal_fin_eq_natCast]
  exact map_natCast (groupRingHom σ hσ) 2

@[simp] theorem diagonal_singleton (x : X) : P.diagonal {x} = 0 := by
  have h := P.price_binaryDiagonal_eq (fun _ : Unit ↦ x)
  rw [P.collapsed, Finset.image_const Finset.univ_nonempty] at h
  exact h.symm

theorem diagonal_pair (x y : X) : P.diagonal {x, y} = dist x y := by
  have h := P.price_binaryDiagonal_eq ![x, y]
  rw [P.wire] at h
  simpa [Finset.univ_fin2] using h.symm

/-- The binary diagonal pays at most one unit of price per unit displacement
of each index, including collisions at either endpoint. -/
theorem diagonal_transport {I : Type} [Fintype I] (p q : I → X) :
    dist (P.diagonal (Finset.univ.image p)) (P.diagonal (Finset.univ.image q)) ≤
      ∑ i, dist (p i) (q i) := by
  cases isEmpty_or_nonempty I with
  | inl => simp
  | inr =>
    rw [← P.price_binaryDiagonal_eq, ← P.price_binaryDiagonal_eq]
    have h := P.transport (Raw.diagonal I K (Fin 2)) p q
    simpa [Raw.diagonal, Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))] using h

/-- Restricting tensor prices along an isometry restricts their finite-set
diagonal to the isometric image. -/
theorem diagonal_pullback {Y : Type*} [MetricSpace Y] (f : Y → X) (hf : Isometry f) (S : Finset Y) :
    (P.pullback f hf).diagonal S = P.diagonal (S.image f) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  let z (i : Fin S.card) := (S.equivFin.symm i).val
  have : Nonempty (Fin S.card) := Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hS)
  have himage : Finset.univ.image (f ∘ z) = S.image f := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (S.equivFin.symm i).prop, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨S.equivFin ⟨y,hy⟩, by simp [z]⟩
  rw [← himage, ← P.price_binaryDiagonal_eq, diagonal, ite_eq_left hS]
  rfl

end SpectralPlacementPrices

end

end SpectralBooks
end LinearAlgebra
end OAI
