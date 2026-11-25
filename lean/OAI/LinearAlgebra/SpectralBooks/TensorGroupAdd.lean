import OAI.LinearAlgebra.SpectralBooks.TensorGroupRaw
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Push

/-! # Grouping a direct sum over occupied sites -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical

namespace SiteTensor.Raw

universe v

variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]

/-- Grouping sends uniform summand tags to uniform tags at every old site in a fiber.
Surjectivity ensures at least one old site is available to distinguish the tags. -/
private def groupedTags (σ : I → J) (hs : Function.Surjective σ) (A B : I → Type v) (j : J) :
    ((∀ t : {i // σ i = j}, A t.1) ⊕ (∀ t : {i // σ i = j}, B t.1)) ↪
      (∀ t : {i // σ i = j}, A t.1 ⊕ B t.1) where
  toFun := Sum.elim (fun a t => Sum.inl (a t)) (fun b t => Sum.inr (b t))
  inj' := by
    obtain ⟨i, hi⟩ := hs j
    intro a b h
    cases a <;> cases b
    · congr 1
      funext t
      exact Sum.inl.inj (congrFun h t)
    · cases congrFun h ⟨i, hi⟩
    · cases congrFun h ⟨i, hi⟩
    · congr 1
      funext t
      exact Sum.inr.inj (congrFun h t)

omit [Fintype J] in
private theorem group_eq_push (σ : I → J) (X : Raw.{v} I K) :
    (X.group σ).coeff = pushCoeff (groupIndexEquiv σ X.Leg) X.coeff := by
  funext x
  exact (pushCoeff_equiv (groupIndexEquiv σ X.Leg) X.coeff x).symm

/-- Grouping sites along a surjection preserves direct sums up to local restriction. -/
theorem group_add_equivalent (σ : I → J) (hs : Function.Surjective σ) (X Y : Raw.{v} I K) :
    ((X.add Y).group σ).Equivalent ((X.group σ).add (Y.group σ)) := by
  let g := groupedTags σ hs X.Leg Y.Leg
  let e := groupIndexEquiv σ (fun i => X.Leg i ⊕ Y.Leg i)
  let S := (X.group σ).add (Y.group σ)
  have h : ((X.add Y).group σ).coeff = pushCoeff (fun x j => g j (x j)) S.coeff := by
    rw [group_eq_push]
    change pushCoeff e (pushCoeff (fun x i => Sum.inl (x i)) X.coeff +
      pushCoeff (fun y i => Sum.inr (y i)) Y.coeff) =
      pushCoeff (fun (x : ∀ j, (X.group σ).Leg j ⊕ (Y.group σ).Leg j) j => g j (x j)) (pushCoeff (fun x j => Sum.inl (x j)) (X.group σ).coeff +
        pushCoeff (fun y j => Sum.inr (y j)) (Y.group σ).coeff)
    rw [group_eq_push, group_eq_push, pushCoeff_add, pushCoeff_add]
    congr 1 <;> (erw [pushCoeff_comp, pushCoeff_comp, pushCoeff_comp]) <;> rfl
  have hg := equivalent_pushCoeff g S.coeff
  unfold Equivalent Restricts
  rw [h]
  exact ⟨hg.2, hg.1⟩

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
