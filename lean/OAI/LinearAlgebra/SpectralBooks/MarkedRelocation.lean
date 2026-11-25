import OAI.LinearAlgebra.SpectralBooks.MarkedPower
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping

/-! # Separating a distinguished factor of a placed tensor

Splitting off an arbitrary index preserves the restriction class after grouping
at the occupied sites. This allows the exterior factorizations to apply to an
update of any single index in a placement.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace SiteTensor.Relocation

variable {I J : Type} {K : Type*} [Fintype I] [Fintype J]

/-- Coefficients of the tensor with factor `i` separated from its complement. -/
def markCoeff (T : Raw.{0} I K) (i : I)
    (x : ∀ j : {j // j ≠ i}, T.Leg j.1) (q : T.Leg i) : K :=
  T.coeff (fun j => if h : j = i then h.symm ▸ q else x ⟨j,h⟩)

/-- Placing the separated factor back at its original index restores the tensor. -/
theorem marked_group_equivalent [DecidableEq I] [CommSemiring K] (T : Raw.{0} I K) (i : I) :
    ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)).group
      (placeMark Subtype.val i)).Equivalent T := by
  classical
  let U := marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)
  let p := placeMark (Subtype.val : {j // j ≠ i} → I) i
  let e (j : I) : (U.group p).Leg j ≃ T.Leg j := {
    toFun := fun z => if h : j = i then h.symm ▸ z ⟨.inr (), h.symm⟩
      else z ⟨.inl ⟨j,h⟩, rfl⟩
    invFun := fun x t => match t with
      | ⟨.inl ⟨k,_⟩,h⟩ => cast (congrArg T.Leg (show j = k from h.symm)) x
      | ⟨.inr (),h⟩ => cast (congrArg T.Leg (show j = i from h.symm)) x
    left_inv := by
      intro z
      funext t
      rcases t with ⟨⟨k,hk⟩ | ⟨⟩,h⟩
      · change k = j at h
        subst j
        simp [hk]
        rfl
      · change i = j at h
        subst j
        simp
        rfl
    right_inv := by
      intro x
      by_cases h : j = i
      · subst j
        simp
        rfl
      · simp [h]
        rfl }
  apply Raw.reindex_equivalent (X := U.group p) (Y := T) e
  intro x
  apply congrArg T.coeff
  funext j
  by_cases h : j = i
  · subst j
    simp [e]
    rfl
  · simp [e,h]
    rfl

/-- The two groupings have the same class at any update of the marked index. -/
theorem ofRaw_update_eq_mark [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I)
    (σ : I → J) (p : J) :
    ofRaw (T.group (Function.update σ i p)) =
      ofRaw ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)).group
        (placeMark (σ ∘ Subtype.val) p)) := by
  classical
  let U := marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)
  let q := placeMark (Subtype.val : {j // j ≠ i} → I) i
  have hp : (Function.update σ i p) ∘ q = placeMark (σ ∘ Subtype.val) p := by
    funext j
    rcases j with ⟨j,h⟩ | ⟨⟩
    · exact Function.update_of_ne h _ _
    · exact Function.update_self ..
  let f := groupClass (K := K) (Function.update σ i p)
  have h : f (ofRaw (U.group q)) = f (ofRaw T) := congrArg f
    (ofRaw_eq_iff.mpr (marked_group_equivalent T i))
  calc
    _ = f (ofRaw (U.group q)) := h.symm
    _ = ofRaw (U.group ((Function.update σ i p) ∘ q)) :=
      ofRaw_eq_iff.mpr (Raw.group_group_equivalent U q (Function.update σ i p))
    _ = _ := congrArg (fun s => ofRaw (U.group s)) hp

/-- Log price at an updated placement, expressed using a separate marked leg. -/
theorem rawLogPrice_update_eq_mark [DecidableEq I] [Nonempty J] [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (T : Raw.{0} I K) (i : I) (σ : I → J) (p : J) :
    rawLogPrice φ c (T.group (Function.update σ i p)) =
      rawLogPrice φ c ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i)
        (markCoeff T i)).group (placeMark (σ ∘ Subtype.val) p)) := by
  simp only [rawLogPrice, ofRaw_update_eq_mark T i σ p]

/-- Changing the basis of the marked leg alone preserves mutual restriction. -/
theorem marked_reindex {A : I → Type} [∀ j, Fintype (A j)] {Q D : Type}
    [Fintype Q] [Fintype D] [CommSemiring K] (T : (∀ j, A j) → Q → K) (e : Q ≃ D) :
    (marked A Q T).Equivalent (marked A D (fun x d => T x (e.symm d))) := by
  let f (k : I ⊕ Unit) : (marked A Q T).Leg k ≃ (marked A D (fun x d => T x (e.symm d))).Leg k := by
    rcases k with k | ⟨⟩
    · exact Equiv.refl _
    · exact e
  apply Raw.reindex_equivalent f
  intro x
  exact congrArg (T (fun j => x (.inl j))) (e.symm_apply_apply _).symm

/-- For any placement, enumerate the selected factor with a finite ordinal. -/
theorem ofRaw_group_eq_markFin [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I)
    {n : ℕ} (e : T.Leg i ≃ Fin n) (σ : I → J) :
    ofRaw (T.group σ) =
      ofRaw ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (Fin n)
        (fun x q => markCoeff T i x (e.symm q))).group (placeMark (σ ∘ Subtype.val) (σ i))) := by
  have h := ofRaw_update_eq_mark T i σ (σ i)
  rw [Function.update_eq_self] at h
  exact h.trans (congrArg (groupClass (K := K) (placeMark (σ ∘ Subtype.val) (σ i)))
    (ofRaw_eq_iff.mpr (marked_reindex (markCoeff T i) e)))

/-- Separating the marked leg preserves nonvanishing. -/
theorem marked_ne_zero [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I) (hT : T.coeff ≠ 0) :
    (marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)).coeff ≠ 0 := by
  let : Nonempty I := ⟨i⟩
  let U := marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)
  let q := placeMark (Subtype.val : {j // j ≠ i} → I) i
  apply (U.group_ne_zero_iff q).mp
  intro hz
  exact hT ((ofRaw_eq_zero_iff T).mp ((ofRaw_eq_iff.mpr (marked_group_equivalent T i)).symm.trans
    ((ofRaw_eq_zero_iff _).mpr hz)))

/-- Enumerating a marked factor preserves nonvanishing. -/
theorem marked_fin_ne_zero [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I) {n : ℕ}
    (e : T.Leg i ≃ Fin n) (hT : T.coeff ≠ 0) :
    (marked (fun j : {j // j ≠ i} => T.Leg j.1) (Fin n)
      (fun x q => markCoeff T i x (e.symm q))).coeff ≠ 0 := by
  intro hz
  exact marked_ne_zero T i hT ((ofRaw_eq_zero_iff _).mp
    ((ofRaw_eq_iff.mpr (marked_reindex (markCoeff T i) e)).trans ((ofRaw_eq_zero_iff _).mpr hz)))

/-- One enumerated marked power gives the powered prices for all placements of
the selected leg, while the background placement stays fixed. -/
theorem exists_finPower_update [DecidableEq I] [Nonempty J] [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (T : Raw.{0} I K) (hT : T.coeff ≠ 0) (i : I) (x : I → J) (n : ℕ) :
    ∃ S : (∀ j : {j // j ≠ i}, Fin n → T.Leg j.1) → Fin ((Fintype.card (T.Leg i))^n) → K,
      (marked _ _ S).coeff ≠ 0 ∧ ∀ p : J,
        rawLogPrice φ c ((marked _ _ S).group (placeMark (x ∘ Subtype.val) p)) =
          n * rawLogPrice φ c (T.group (Function.update x i p)) := by
  refine ⟨finPowerCoeff n (markCoeff T i), marked_finPower_ne_zero n _ (marked_ne_zero T i hT), ?_⟩
  intro p
  rw [rawLogPrice_marked_finPower, rawLogPrice_update_eq_mark φ c T i x p]

end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
