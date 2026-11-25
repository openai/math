import OAI.Computability.NearSquareRoot.SynchronizedPlacedLayers
import OAI.Computability.NearSquareRoot.SynchronizedWord
import OAI.Computability.NearSquareRoot.SynchronizedBorrowedPass
import OAI.Computability.NearSquareRoot.SynchronizedAuxiliaryLayout

/-! Actual matrix words for a batch of restored short transforms. Each primitive
factor executes on all its placements, with the identity on every unused cell.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPair SynchronizedPadding SynchronizedBorrowing

noncomputable section

variable {A J P : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    [Fintype P] [DecidableEq P]

private abbrev Spare {D : Type} (e : D ↪ P) := {p : P // p ∉ Set.range e}

private def fill {D : Type} (e : D ↪ P) : D ⊕ Spare e ≃ P := by
  classical
  exact ((Equiv.ofInjective e e.injective).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl _)

omit [Fintype P] [DecidableEq P] in
private theorem fill_inl {D : Type} (e : D ↪ P) (t : D) : fill e (.inl t) = e t := rfl
omit [Fintype P] [DecidableEq P] in
private theorem fill_inr {D : Type} (e : D ↪ P) (t : Spare e) : fill e (.inr t) = t.val := rfl

/-- Matrix action of parallel copies at any disjoint placement. -/
def placeHom (e : A × J ↪ P) : Matrix A A ℂ →* Matrix P P ℂ := by
  classical
  let F (M : Matrix A A ℂ) : Matrix (A × J) (A × J) ℂ := blockDiagonal fun _ ↦ M
  refine
    { toFun := fun M ↦ (axisPadding (b := Spare e) (F M)).submatrix (fill e).symm (fill e).symm
      map_one' := ?_
      map_mul' := ?_ }
  · have h : F 1 = 1 := blockDiagonal_one
    simp only [h, axisPadding, fromBlocks_one, submatrix_one_equiv]
  · intro M N
    have h := blockDiagonal_mul (fun _ : J ↦ M) (fun _ : J ↦ N)
    simp only [F, h, submatrix_mul_equiv, axisPadding, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add]

theorem ShortLayer.place {M : Matrix A A ℂ} (h : ShortLayer M) (e : A × J ↪ P)
    (he : Even (Fintype.card P)) : ShortLayer (placeHom e M) := by
  classical
  have he' := Fintype.card_congr (fill e)
  rw [Fintype.card_sum] at he'
  exact (h.copies.withUnused (he' ▸ he)).relocate (fill e)

theorem HasShortWord.place {M : Matrix A A ℂ} {n : ℕ} (h : HasShortWord M n)
    (e : A × J ↪ P) (he : Even (Fintype.card P)) : HasShortWord (placeHom e M) n := by
  obtain ⟨w, rfl, hw, hn⟩ := h
  refine ⟨w.map (placeHom e), (map_list_prod _ _).symm, ?_, by simpa using hn⟩
  intro m hm
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
  exact (hw v hv).place e he

theorem HasShortWord.relocate {M : Matrix A A ℂ} {n : ℕ} (h : HasShortWord M n)
    (f : A ≃ P) : HasShortWord (M.submatrix f.symm f.symm) n := by
  obtain ⟨w,rfl,hw,hn⟩ := h
  let g := (Matrix.reindexRingEquiv ℂ f).toMonoidHom
  refine ⟨w.map g, (map_list_prod g _).symm, ?_, by simpa using hn⟩
  intro m hm
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
  exact (hw v hv).relocate f

omit [DecidableEq A] in
theorem copies_apply (M : Matrix A A ℂ) (x : A × J → ℂ) (p : A × J) :
    (blockDiagonal (fun _ : J ↦ M) *ᵥ x) p = (M *ᵥ fun a ↦ x (a,p.2)) p.1 := by
  classical
  simp [mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply,
    ite_mul, Finset.sum_ite_eq]

theorem placeHom_mulVec (M : Matrix A A ℂ) (e : A × J ↪ P) (x : P → ℂ) :
    placeHom e M *ᵥ x = Function.extend e (fun p ↦ (M *ᵥ fun t ↦ x (e (t,p.2))) p.1) x := by
  classical
  change (axisPadding (b := Spare e) (blockDiagonal fun _ : J ↦ M)).submatrix
      (fill e).symm (fill e).symm *ᵥ x = _
  rw [submatrix_mulVec_equiv, axisPadding, fromBlocks_mulVec]
  funext p
  obtain ⟨p | u, rfl⟩ := (fill e).surjective p
  · simp only [Function.comp_apply, Equiv.symm_apply_apply]
    simp [Function.comp_def, fill_inl, copies_apply, e.injective.extend_apply]
  · simp only [Function.comp_apply, Equiv.symm_apply_apply]
    simp [Function.comp_def, fill_inr, Function.extend_apply' _ _ _ u.property]

end

end ShortFourier

end NearSquareRoot
end Computability
end OAI
