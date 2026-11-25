import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetPolynomial
import Mathlib.Logic.Equiv.Bool
import Mathlib.Tactic

/-! # Incidence subdivision and the signed projection to independent sets

The left vertices are the original vertices and the right vertices are the
original edges. Summing a right vertex of weights (1,-1) enforces coverage
by an endpoint. Complementing the original bits turns a vertex cover into an
independent set.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace IndependentSetGraph

open scoped Classical BigOperators

variable {m n : ℕ} {R : Type*} [CommRing R]

/-- Bipartite incidence after subdividing every edge once. -/
def incidence (l r : Fin n → Fin m) (i : Fin m) (e : Fin n) : Prop := l e = i ∨ r e = i

private def edgeTerm (a b c : Bool) : R :=
  if c then (if a || b then 0 else -1) else 1

private theorem sum_edgeTerm (a b : Bool) :
    (∑ c, edgeTerm (R := R) a b c) = if a || b then 1 else 0 := by
  cases a <;> cases b <;> simp [edgeTerm]

private theorem incidenceTerm (l r : Fin n → Fin m) (a : Fin m → Bool) (c : Fin n → Bool) :
    (if IndependentSetGrid.Independent (incidence l r) (a,c) then
      ∏ j, (if c j then (-1:R) else 1) else 0) = ∏ e, edgeTerm (a (l e)) (a (r e)) (c e) := by
  have term (j) : edgeTerm (a (l j)) (a (r j)) (c j) =
      (if c j then (-1:R) else 1) *
        (if c j = true → a (l j) = false ∧ a (r j) = false then 1 else 0) := by
    cases ha : a (l j) <;> cases hb : a (r j) <;> cases hc : c j <;> simp_all [edgeTerm]
  simp_rw [term, Finset.prod_mul_distrib, Fintype.prod_boole]
  have iffcond : IndependentSetGrid.Independent (incidence l r) (a,c) ↔
      ∀ i, c i = true → a (l i) = false ∧ a (r i) = false := by
    constructor
    · intro h e he
      constructor
      · cases ha : a (l e)
        · rfl
        · exact False.elim (h _ _ (Or.inl rfl) ha he)
      · cases ha : a (r e)
        · rfl
        · exact False.elim (h _ _ (Or.inr rfl) ha he)
    · intro h i e hi ha he
      rcases hi with hli | hri
      · exact Bool.noConfusion ((hli ▸ (h e he).1).symm.trans ha)
      · exact Bool.noConfusion ((hri ▸ (h e he).2).symm.trans ha)
  rw [iffcond]
  split <;> simp

/-- The unsigned endpoint bits on the subdivided graph have the two weights
interchanged. The internal edge vertices have weights (1,-1). -/
theorem generatingSum_incidence (l r : Fin n → Fin m) (w : Fin m → Bool → R) :
    IndependentSetGrid.generatingSum (incidence l r) (fun i b => w i (!b))
      (fun _ b => if b then -1 else 1) = weightedSum l r w := by
  classical
  unfold IndependentSetGrid.generatingSum weightedSum
  rw [Fintype.sum_prod_type]
  let e : (Fin m → Bool) ≃ (Fin m → Bool) := Equiv.piCongrRight (fun _ => Equiv.boolNot)
  have heq : (fun a b : Fin m => Classical.propDecidable (a = b)) = instDecidableEqFin m :=
    Subsingleton.elim _ _
  rw [heq]
  apply Fintype.sum_equiv e
  intro a
  let W := ∏ i, w i (!(a i))
  have row (c : Fin n → Bool) :
      (if IndependentSetGrid.Independent (incidence l r) (a,c) then
        W * ∏ j, (if c j then (-1:R) else 1) else 0) =
        W * ∏ i, edgeTerm (a (l i)) (a (r i)) (c i) := by
    rw [← incidenceTerm l r]
    split <;> simp
  change (∑ c : Fin n → Bool, if IndependentSetGrid.Independent (incidence l r) (a,c) then
    W * ∏ j, (if c j then (-1:R) else 1) else 0) = _
  simp_rw [row, ← Finset.mul_sum, ← Fintype.prod_sum, sum_edgeTerm, Fintype.prod_boole]
  have hgood : (∀ i, (a (l i) || a (r i)) = true) ↔ independent l r (e a) := by
    simp only [independent]
    change _ ↔ ∀ i, (!a (l i)) = true → (!a (r i)) ≠ true
    constructor
    · intro h i
      have hi := h i
      cases hl : a (l i) <;> cases hr : a (r i) <;> simp_all
    · intro h i
      have hi := h i
      cases hl : a (l i) <;> cases hr : a (r i) <;> simp_all
  by_cases hh : independent l r (e a)
  · simp [hgood.mpr hh, hh, W, e]
  · have hbad := fun hc => hh (hgood.mp hc)
    simp only [ite_eq_right_of_eq_false _ _ (eq_false hbad), mul_zero, ite_eq_right_of_eq_false _ _ (eq_false hh)]


variable {V E : Type*} [Fintype V] [Fintype E]

private def endpoint (l : E → V) (j : Fin (Fintype.card E)) : Fin (Fintype.card V) :=
  Fintype.equivFin V (l ((Fintype.equivFin E).symm j))

/-- Incidence graph numbered on finite ordinals. -/
def numberedIncidence (l r : E → V) := incidence (endpoint l) (endpoint r)

/-- The old vertex bit is complemented. The subdividing vertices have weights (1,-1). -/
def numberedProjection :
    ((Fin (Fintype.card V) ⊕ Fin (Fintype.card E)) × Bool) → ProjectionAtom R (V × Bool)
  | (.inl i, b) => .inl ((Fintype.equivFin V).symm i, !b)
  | (.inr _, b) => .inr (if b then -1 else 1)

private theorem weightedSum_endpoint (l r : E → V) (w : V → Bool → R) :
    weightedSum (endpoint l) (endpoint r) (fun i => w ((Fintype.equivFin V).symm i)) =
      weightedSum l r w := by
  classical
  let e := Fintype.equivFin V
  let a : (Fin (Fintype.card V) → Bool) ≃ (V → Bool) :=
    e.symm.arrowCongr (Equiv.refl Bool)
  unfold weightedSum
  have hfin : (fun i j : Fin (Fintype.card V) => Classical.propDecidable (i = j)) =
      instDecidableEqFin (Fintype.card V) := Subsingleton.elim _ _
  rw [hfin]
  apply Fintype.sum_equiv a
  intro x
  have hc : independent (endpoint l) (endpoint r) x ↔ independent l r (a x) := by
    change (∀ j, x (e (l ((Fintype.equivFin E).symm j))) = true →
      x (e (r ((Fintype.equivFin E).symm j))) ≠ true) ↔
      (∀ j, x (e (l j)) = true → x (e (r j)) ≠ true)
    constructor
    · intro h j
      simpa using h (Fintype.equivFin E j)
    · intro h j
      exact h ((Fintype.equivFin E).symm j)
  rw [hc]
  split
  · apply Fintype.prod_equiv e.symm
    intro i
    change w (e.symm i) (x i) = w (e.symm i) (x (e (e.symm i)))
    rw [e.apply_symm_apply]
  · rfl

theorem project_numbered_polynomial (l r : E → V) :
    project (numberedProjection (R := R) (V := V) (E := E))
      (IndependentSetGrid.polynomial (numberedIncidence l r)) = polynomial R l r := by
  classical
  have map_eq : ∀ (p : (Fin (Fintype.card V) ⊕ Fin (Fintype.card E)) × Bool →
      ProjectionAtom R (V × Bool)), project p (IndependentSetGrid.polynomial (numberedIncidence l r)) =
      IndependentSetGrid.generatingSum (numberedIncidence l r)
        (fun i b => atomPolynomial (p (.inl i,b))) (fun j b => atomPolynomial (p (.inr j,b))) := by
    intros
    simp [project, IndependentSetGrid.polynomial, IndependentSetGrid.generatingSum,
      map_sum, apply_ite, map_prod]
  rw [map_eq]
  convert (generatingSum_incidence (endpoint l) (endpoint r)
    (fun i b => MvPolynomial.X ((Fintype.equivFin V).symm i,b) :
      Fin (Fintype.card V) → Bool → MvPolynomial (V × Bool) R)).trans
    (weightedSum_endpoint l r (fun i b => MvPolynomial.X (i,b))) using 1
  · apply congrArg
    funext j b
    cases b <;> simp [numberedProjection, atomPolynomial]
  · rfl

theorem row_degree_le (l r : E → V) (D : ℕ)
    (hdegree : ∀ v, Fintype.card {e // l e = v ∨ r e = v} ≤ D) (i : Fin (Fintype.card V)) :
    Fintype.card {j // numberedIncidence l r i j} ≤ D := by
  let f : {j // numberedIncidence l r i j} →
      {e // l e = (Fintype.equivFin V).symm i ∨ r e = (Fintype.equivFin V).symm i} :=
    fun j => ⟨(Fintype.equivFin E).symm j, j.property.imp
      (fun h => (Fintype.equivFin V).eq_symm_apply.mpr h)
      (fun h => (Fintype.equivFin V).eq_symm_apply.mpr h)⟩
  exact (Fintype.card_le_of_injective f (fun _ _ h =>
    Subtype.ext ((Fintype.equivFin E).symm.injective (congrArg Subtype.val h)))).trans (hdegree _)

theorem column_degree_le (l r : E → V) (j : Fin (Fintype.card E)) :
    Fintype.card {i // numberedIncidence l r i j} ≤ 2 := by
  classical
  let f (i : {i // numberedIncidence l r i j}) : Bool := decide (endpoint l j = i.1)
  have hinj : Function.Injective f := by
    intro a b h
    change decide (endpoint l j = a.1) = decide (endpoint l j = b.1) at h
    have he : endpoint l j = a.1 ↔ endpoint l j = b.1 := by simpa using h
    have ha := a.property
    have hb := b.property
    change endpoint l j = a.1 ∨ endpoint r j = a.1 at ha
    change endpoint l j = b.1 ∨ endpoint r j = b.1 at hb
    apply Subtype.ext
    by_cases hla : endpoint l j = a.1
    · exact hla.symm.trans (he.mp hla)
    · exact (ha.resolve_left hla).symm.trans (hb.resolve_left (hla ∘ he.mpr))
  simpa using Fintype.card_le_of_injective f hinj

end IndependentSetGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
