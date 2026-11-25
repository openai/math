import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementTerm
import OAI.LinearAlgebra.SpectralBooks.PortGraph.BoundedPatchReplacementPrescribed

/-! # The record-indexed list of planar replacements

The canonical spanning-tree contour determines all boundary indices. The
symbolic patch program uses one variable per old vertex table entry. Renaming
these variables to the addresses of the shared tables preserves formula weight.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace PortGraph.PatchShape

open PlanarPatch Arithmetic UniformDecorations MvPolynomial

private theorem hasFormula_relabel {F I J : Type*} [Field F] (f : I → J) {C : ℕ}
    {p : MvPolynomial I F} (hp : HasFormula C p) :
    HasFormula C (eval₂Hom MvPolynomial.C (fun i => X (f i)) p) := by
  obtain ⟨e,rfl,hc⟩ := hp
  have go (t : Expression F I) : ∃ t' : Expression F J, expressionPolynomial t' =
      eval₂Hom MvPolynomial.C (fun i => X (f i)) (expressionPolynomial t) ∧ t'.cost = t.cost := by
    induction t with
    | constant c => exact ⟨.constant c, by simp only [expressionPolynomial, eval₂Hom_C],rfl⟩
    | input i => exact ⟨.input (f i), by simp only [expressionPolynomial, eval₂Hom_X'],rfl⟩
    | add l r il ir =>
      obtain ⟨a,ha,ca⟩ := il
      obtain ⟨b,hb,cb⟩ := ir
      exact ⟨.add a b, by simp only [expressionPolynomial, map_add, ha, hb],
        by simp [Expression.cost, ca, cb]⟩
    | sub l r il ir =>
      obtain ⟨a,ha,ca⟩ := il
      obtain ⟨b,hb,cb⟩ := ir
      exact ⟨.sub a b, by simp only [expressionPolynomial, map_sub, ha, hb],
        by simp [Expression.cost, ca, cb]⟩
    | mul l r il ir =>
      obtain ⟨a,ha,ca⟩ := il
      obtain ⟨b,hb,cb⟩ := ir
      exact ⟨.mul a b, by simp only [expressionPolynomial, map_mul, ha, hb],
        by simp [Expression.cost, ca, cb]⟩
  obtain ⟨u,hu,hcost⟩ := go e
  exact ⟨u,hu, hcost ▸ hc⟩

private theorem tree_formula_map {F I J V : Type*} [Field F] {d : V → ℕ}
    (f : I → J) {q C : ℕ} (t : TrivalentTree (MvPolynomial I F) d q) (hf : t.FormulaBound C) :
    (t.map (eval₂Hom MvPolynomial.C (fun i => X (f i)))).FormulaBound C := by
  induction t with
  | port => exact fun e => nomatch e
  | branch B l r hl hr =>
    rintro (⟨i,a,b⟩ | (e | e))
    · exact hasFormula_relabel f (hf (.inl (i,a,b)))
    · exact hl (fun e => hf (.inr (.inl e))) e
    · exact hr (fun e => hf (.inr (.inr e))) e

/-- The same list-length constant works for every valid shape and every old
width. In the direct case the list has precisely one element, even on the
scalar patch. List indices remain distinguishable if two tree tensors agree. -/
theorem recordCatalogue {F : Type} [Field F]
    (noPlane : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))))
    (K : ℕ) (hK : 0 < K) :
    ∃ c : ℕ, ∀ (R : PatchShape K) (hc : R.InternallyConnected) (w : ℕ),
      ∃ (L : ℕ) (u : Fin L → R.RecordTerm hc w F), L ≤ 2^(w+c) ∧
        ∀ x, R.oldValue (fun θ a => X ⟨θ,a⟩) x = ∑ j, (u j).value x := by
  obtain ⟨c,hc⟩ := ordered_patch_replacement noPlane K hK
  refine ⟨c,?_⟩
  intro R hconn w
  by_cases small : Fintype.card R.Stub ≤ 3
  · refine ⟨1, fun _ => .direct small, Nat.one_le_pow _ _ (by decide), ?_⟩
    intro x
    simp [RecordTerm.value]
  let b := Fintype.card R.Stub - 1
  have card : Fintype.card R.Stub = b+1 := by dsimp [b]; omega
  let e := R.contourSlots hconn card
  let G := R.toPiece.graph
  let A := R.toPiece.attach
  obtain ⟨L,trees,hL,ht,hf,he,-⟩ := hc G A w b e (by
    change Fintype.card (Fin R.size.val) ≤ K
    simpa using Nat.le_of_lt_succ R.size.isLt) R.total_degree_le (by omega)
  let addr (i : G.PatchEntry A (2^w)) := R.oldAddress i.1 i.2.1 i.2.2
  let U (θ : MapType) (a : Fin θ.degree.val → Bits w) : MvPolynomial (Address w) F := X ⟨θ,a⟩
  let φ := eval₂Hom MvPolynomial.C (fun i => X (R := F) (addr i))
  let u (j : Fin L) : R.RecordTerm hconn w F :=
    .pruned card (by omega) ((trees j).map φ) (by simpa using (ht j).1)
      (by simpa using (ht j).2.1) (by simpa using (ht j).2.2)
      (fun e => ((tree_formula_map addr _ (hf j)) e).mono (Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul_right _ (Nat.le_max_right ..))))
  exact ⟨L,u,hL,fun x => he MvPolynomial.C (R.oldTable U) x⟩

end PortGraph.PatchShape

end

end SpectralBooks
end LinearAlgebra
end OAI
