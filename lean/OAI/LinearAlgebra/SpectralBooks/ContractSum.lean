import OAI.LinearAlgebra.SpectralBooks.ContractionPrice

/-! # Contraction of a block direct sum -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

universe v
variable {I : Type*}

private abbrev extendIndex {L : Option I → Type v} (b : L none) (a : ∀ i, L (some i)) :
    ∀ j, L j := Equiv.piOptionEquivProd.symm (b, a)

private theorem extendIndex_inl {A B : Option I → Type v} (b : A none) (a : ∀ i, A (some i)) :
    extendIndex (L := fun j => A j ⊕ B j) (Sum.inl b) (fun i => Sum.inl (a i)) =
      (fun j => Sum.inl (extendIndex b a j)) := by
  funext j
  cases j <;> rfl

private theorem extendIndex_inr {A B : Option I → Type v} (b : B none) (a : ∀ i, B (some i)) :
    extendIndex (L := fun j => A j ⊕ B j) (Sum.inr b) (fun i => Sum.inr (a i)) =
      (fun j => Sum.inr (extendIndex b a j)) := by
  funext j
  cases j <;> rfl

variable {K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- Contracting the new site of a direct sum contracts each of its two blocks
against the corresponding part of the covector. -/
theorem ofRaw_contractNew_add (X Y : Raw.{v} (Option I) K) (ξ : X.Leg none ⊕ Y.Leg none → K) :
    ofRaw ((X.add Y).contractNew ξ) =
      ofRaw (X.contractNew (ξ ∘ Sum.inl)) + ofRaw (Y.contractNew (ξ ∘ Sum.inr)) := by
  classical
  rw [← ofRaw_add, ofRaw_eq_iff]
  apply Raw.reindex_equivalent (X := (X.add Y).contractNew ξ)
    (Y := (X.contractNew (ξ ∘ Sum.inl)).add (Y.contractNew (ξ ∘ Sum.inr)))
    (fun _ => Equiv.refl _)
  intro (a : ∀ i, X.Leg (some i) ⊕ Y.Leg (some i))
  change (∑ z : X.Leg none ⊕ Y.Leg none, ξ z * sumCoeff X.coeff Y.coeff
    (extendIndex (L := fun j => X.Leg j ⊕ Y.Leg j) z a)) =
      sumCoeff (fun x => ∑ b, ξ (Sum.inl b) * X.coeff (extendIndex b x))
        (fun y => ∑ b, ξ (Sum.inr b) * Y.coeff (extendIndex b y)) a
  rw [Fintype.sum_sum_type]
  by_cases hl : ∃ x : ∀ i, X.Leg (some i), (fun i => Sum.inl (x i)) = a
  · obtain ⟨x, rfl⟩ := hl
    rw [sumCoeff_inl]
    simp_rw [extendIndex_inl, sumCoeff_inl]
    have hm (b : Y.Leg none) : sumCoeff X.coeff Y.coeff
        (extendIndex (L := fun j => X.Leg j ⊕ Y.Leg j) (Sum.inr b) (fun i => Sum.inl (x i))) = 0 := by
      apply sumCoeff_mixed
      · intro z hz
        cases congrFun hz none
      · intro z hz
        cases congrFun hz (some (Classical.arbitrary I))
    simp [hm]
  by_cases hr : ∃ y : ∀ i, Y.Leg (some i), (fun i => Sum.inr (y i)) = a
  · obtain ⟨y, rfl⟩ := hr
    rw [sumCoeff_inr]
    simp_rw [extendIndex_inr, sumCoeff_inr]
    have hm (b : X.Leg none) : sumCoeff X.coeff Y.coeff
        (extendIndex (L := fun j => X.Leg j ⊕ Y.Leg j) (Sum.inl b) (fun i => Sum.inr (y i))) = 0 := by
      apply sumCoeff_mixed
      · intro z hz
        cases congrFun hz (some (Classical.arbitrary I))
      · intro z hz
        cases congrFun hz none
    simp [hm]
  have hm (b : X.Leg none ⊕ Y.Leg none) : sumCoeff X.coeff Y.coeff
      (extendIndex (L := fun j => X.Leg j ⊕ Y.Leg j) b a) = 0 := by
    apply sumCoeff_mixed
    · intro z hz
      exact hl ⟨fun i => z (some i), funext fun i => congrFun hz (some i)⟩
    · intro z hz
      exact hr ⟨fun i => z (some i), funext fun i => congrFun hz (some i)⟩
  rw [sumCoeff_mixed _ _ a (not_exists.mp hl) (not_exists.mp hr)]
  simp [hm]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
