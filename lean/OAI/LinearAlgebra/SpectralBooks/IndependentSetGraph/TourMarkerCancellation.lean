import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetPolynomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Forcing an occupied option at each position by signed markers -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace IndependentSetGraph

open scoped Classical BigOperators
noncomputable section

variable {O T E R : Type*} [Fintype O] [Fintype T] [CommRing R]

abbrev markedLeft (left : E → O) : E ⊕ O → O ⊕ T :=
  Sum.elim (Sum.inl ∘ left) Sum.inl

abbrev markedRight (right : E → O) (pos : O → T) : E ⊕ O → O ⊕ T :=
  Sum.elim (Sum.inl ∘ right) (Sum.inr ∘ pos)

def markedWeight (w : O → R) : O ⊕ T → Bool → R :=
  Sum.elim (fun o b => if b then w o else 1) (fun _ b => if b then -1 else 1)

/-- After summing the marker bits, a covered position contributes one and
an uncovered position contributes zero, in every characteristic. -/
theorem marked_weightedSum (left right : E → O) (pos : O → T) (w : O → R) :
    weightedSum (markedLeft left) (markedRight right pos) (markedWeight w) =
      ∑ x : O → Bool, if independent left right x ∧ (∀ t, ∃ o, pos o = t ∧ x o = true) then
        ∏ o, (if x o then w o else 1) else 0 := by
  let occ (x : O → Bool) (t : T) : Prop := ∃ o, pos o = t ∧ x o = true
  let v (x : O → Bool) (t : T) (y : Bool) : R :=
    if occ x t → y ≠ true then (if y then -1 else 1) else 0
  have hmark (x : O → Bool) : (∑ y : T → Bool, ∏ t, v x t (y t)) = if ∀ t, occ x t then 1 else 0 := by
    rw [← Fintype.prod_sum]
    have hf (t : T) : (∑ y, v x t y) = if occ x t then 1 else 0 := by
      by_cases ht : occ x t <;> simp [v, ht]
    simp only [hf]
    exact Fintype.prod_boole
  let eqv := (Equiv.sumArrowEquivProdArrow O T Bool).symm
  let F (b : O ⊕ T → Bool) := if independent (markedLeft left) (markedRight right pos) b then
    ∏ i, markedWeight w i (b i) else 0
  trans (∑ b, F b)
  · unfold weightedSum F
    congr 1
    ext b
    simp
  rw [← eqv.sum_comp F, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have hi (y : T → Bool) :
      independent (markedLeft left) (markedRight right pos) (eqv (x,y)) ↔
        independent left right x ∧ ∀ t, occ x t → y t ≠ true := by
    change (∀ e : E ⊕ O, _) ↔ _
    rw [Sum.forall]
    change (_ ∧ ∀ o, x o = true → y (pos o) ≠ true) ↔ _
    apply and_congr_right
    intro _
    exact ⟨fun h t ⟨o, he, hx⟩ => he ▸ h o hx, fun h o ho => h _ ⟨o,rfl,ho⟩⟩
  let W := ∏ o, (if x o then w o else 1)
  have hterm (y : T → Bool) :
      F (eqv (x,y)) = if independent left right x then W * ∏ t, v x t (y t) else 0 := by
    simp only [F, hi, Fintype.prod_sum_type, markedWeight, Sum.elim_inl, Sum.elim_inr,
      eqv, Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr]
    rw [show (∏ t, v x t (y t)) = if ∀ t, occ x t → y t ≠ true then
        ∏ t, (if y t then (-1:R) else 1) else 0 from Fintype.prod_ite_zero ..]
    split_ifs <;> simp_all [W]
    congr 1
  simp only [hterm]
  by_cases h : independent left right x
  · simp only [h, ite_true, true_and, ← Finset.mul_sum, hmark]
    by_cases hz : ∀ t, occ x t <;> simp [occ] at hz ⊢ <;> simp_all [occ, W]
  · simp [h]

/-- Occupied options carry the prescribed projection atoms, and a selected
marker has weight minus one. -/
def markedProjection {σ : Type*} (w : O → ProjectionAtom R σ) :
    (O ⊕ T) × Bool → ProjectionAtom R σ
  | (.inl o, true) => w o
  | (.inr _, true) => .inr (-1)
  | (_, false) => .inr 1

theorem project_markedPolynomial {σ : Type*} (left right : E → O)
    (pos : O → T) (w : O → ProjectionAtom R σ) :
    project (markedProjection w) (polynomial R (markedLeft left) (markedRight right pos)) =
      ∑ x : O → Bool, if independent left right x ∧ (∀ t, ∃ o, pos o = t ∧ x o = true) then
        ∏ o, (if x o then atomPolynomial (w o) else 1) else 0 := by
  rw [project_polynomial]
  have hw : (fun (v : O ⊕ T) b => atomPolynomial (markedProjection w (v,b))) =
      markedWeight (fun o => atomPolynomial (w o)) := by
    funext v b
    cases v <;> cases b <;> simp [markedProjection, markedWeight, atomPolynomial]
  rw [hw, marked_weightedSum]


end
end IndependentSetGraph

end SpectralBooks
end LinearAlgebra
end OAI
