import OAI.Hierarchy.GridGraph
import OAI.Hierarchy.ConnectedCut
import OAI.Hierarchy.GraphProjection

namespace OAI
/-! # Every balanced bipartition of a square grid cuts a growing number of edges -/

namespace Hierarchy.SquareGrid

open IncidenceGraph
open scoped Classical

/-- Include a fixed grid in the top left of every larger grid. -/
def embed {n m : ℕ} (h : n ≤ m) : (graph n).Embedding (graph m) where
  vertex := (Fin.castLEEmb h).prodMap (Fin.castLEEmb h)
  edge := ((Fin.castLEEmb h).prodMap (Fin.castLEEmb (Nat.sub_le_sub_right h 1))).sumMap
    ((Fin.castLEEmb h).prodMap (Fin.castLEEmb (Nat.sub_le_sub_right h 1)))
  map_left := by rintro (e|e) <;> rfl
  map_right := by rintro (e|e) <;> rfl

private theorem line_crosses {n : ℕ} (P : Fin n → Prop) {u v : Fin n} (hu : P u) (hv : ¬P v) :
    ∃ e : (path n).E, ¬ (P ((path n).left e) ↔ P ((path n).right e)) := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter P
  have test (i : Fin n) : i∈A ↔ P i :=
    ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  obtain ⟨e, he⟩ := (path n).boundary_nonempty_of_connected A (path_connected n u v)
    ((test u).mpr hu) (fun h => hv ((test v).mp h))
  simp only [boundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  exact ⟨e, fun same => he ((test _).trans (same.trans (test _).symm))⟩

private noncomputable def mixed {n : ℕ} (S : Finset (graph n).V) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (∃ j : Fin n, (i,j) ∈ S) ∧ ∃ j : Fin n, (i,j) ∉ S)

private theorem mixed_le {n : ℕ} (S : Finset (graph n).V) :
    (mixed S).card ≤ ((graph n).boundaryEdges S).card := by
  classical
  have select (r : {i // i ∈ mixed S}) :
      ∃ e : (path n).E, ¬ ((r.val,(path n).left e) ∈ S ↔ (r.val,(path n).right e) ∈ S) := by
    obtain ⟨⟨u,hu⟩,v,hv⟩ := (Finset.mem_filter.mp r.property).2
    exact line_crosses (fun j => (r.val,j) ∈ S) hu hv
  let f (r : {i // i ∈ mixed S}) : {e // e ∈ (graph n).boundaryEdges S} :=
    ⟨Sum.inl (r.val,(select r).choose),Finset.mem_filter.mpr ⟨Finset.mem_univ _, (select r).choose_spec⟩⟩
  have inj : Function.Injective f := by
    intro r s eqn
    exact Subtype.ext (congrArg Prod.fst (Sum.inl.inj (congrArg Subtype.val eqn)))
  simpa using Fintype.card_le_of_injective f inj

private theorem all_columns {n : ℕ} (S : Finset (graph n).V) (u v : Fin n)
    (yes : ∀ j : Fin n, (u,j) ∈ S) (no : ∀ j : Fin n, (v,j) ∉ S) :
    n ≤ ((graph n).boundaryEdges S).card := by
  classical
  let edge (j : Fin n) := (line_crosses (fun r => (r,j) ∈ S) (yes j) (no j)).choose
  let f (j : Fin n) : {e // e ∈ (graph n).boundaryEdges S} :=
    ⟨Sum.inr (j,edge j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (line_crosses (fun r => (r,j) ∈ S) (yes j) (no j)).choose_spec⟩⟩
  have inj : Function.Injective f := by
    intro i j eqn
    exact congrArg Prod.fst (Sum.inr.inj (congrArg Subtype.val eqn))
  simpa using Fintype.card_le_of_injective f inj

/-- Each side contains at least a third of the vertices. Either two
opposite monochromatic rows force all columns to cross, or one entire
side lies in rows that each have a horizontal crossing. -/
theorem balanced_cut {n : ℕ} (S : Finset (graph n).V)
    (low : n^2 ≤ 3*S.card) (high : n^2 ≤ 3*Sᶜ.card) :
    n ≤ 3*((graph n).boundaryEdges S).card := by
  classical
  by_cases ne : n=0
  · simp [ne]
  have pos : 0<n := Nat.pos_of_ne_zero ne
  have bound {T : Finset (graph n).V} (size : n^2 ≤ 3*T.card)
      (cover : T ⊆ (mixed S) ×ˢ (Finset.univ : Finset (Fin n))) :
      n ≤ 3*((graph n).boundaryEdges S).card := by
    have product : ((mixed S) ×ˢ (Finset.univ : Finset (Fin n))).card = (mixed S).card*n :=
      (Finset.card_product _ _).trans (by simp)
    have count := (Finset.card_le_card cover).trans_eq product
    have gap := (Nat.le_of_mul_le_mul_right (a:=n) (b:=3*(mixed S).card)
      (show n*n ≤ (3*(mixed S).card)*n by
        rw [←pow_two, Nat.mul_assoc]
        exact size.trans (Nat.mul_le_mul_left 3 count)) pos)
    exact gap.trans (Nat.mul_le_mul_left 3 (mixed_le S))
  by_cases white : ∃ r : Fin n, ∀ j : Fin n, (r,j)∈S
  · obtain ⟨r,hr⟩ := white
    by_cases black : ∃ b : Fin n, ∀ j : Fin n, (b,j)∉S
    · obtain ⟨b,hb⟩ := black
      have cuts := all_columns S r b hr hb
      omega
    · apply bound high
      intro v hv
      have notIn : v∉S := Finset.mem_compl.mp hv
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ⟨v.2, notIn⟩⟩, Finset.mem_univ _⟩
      simpa only [not_forall,not_not] using (not_exists.mp black v.1)
  · apply bound low
    rintro ⟨i,j⟩ hij
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨j,hij⟩,?_⟩, Finset.mem_univ _⟩
    exact not_forall.mp (not_exists.mp white i)

end Hierarchy.SquareGrid

end OAI
