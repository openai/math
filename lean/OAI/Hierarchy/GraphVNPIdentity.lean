import OAI.Hierarchy.GraphVNPSelector

namespace OAI
/-! # Recovering a contraction by summing its Boolean witnesses -/

namespace Hierarchy.IncidenceGraph

open Computability.VPVNP MvPolynomial
open scoped Classical

variable (G : IncidenceGraph) {q : ℕ}

/-- Encode an edge labeling by setting exactly its selected bit at each edge. -/
def encodeLabeling (a : G.E → Fin q) (x : G.Witness q) : Bool :=
  decide (x.2 = a x.1)

private theorem matches_encode (a : G.E → Fin q) (e : G.E) (i : Fin q) :
    G.Matches (G.encodeLabeling a) e i ↔ i=a e := by
  constructor
  · intro h
    have hbit := h i
    simpa [encodeLabeling] using hbit
  · rintro rfl j
    rfl

private theorem encodeLabeling_injective : Function.Injective (G.encodeLabeling (q:=q)) := by
  intro a b eqn
  funext e
  have hit : G.Matches (G.encodeLabeling a) e (b e) := by
    rw [eqn]
    exact (G.matches_encode b e _).mpr rfl
  exact ((G.matches_encode a e _).mp hit).symm

variable (F : Type*) [Field F]

private theorem witness_encoded (a : G.E → Fin q) :
    witnessValue (G.encodeLabeling a) (G.witnessPolynomial F q) = G.assignmentMonomial F a := by
  classical
  rw [witnessPolynomial, map_prod, assignmentMonomial]
  apply Finset.prod_congr rfl
  intro v _
  rw [eval_tablePolynomial]
  have matchRow (t : G.Incident v → Fin q) :
      (∀ e : G.Incident v, G.Matches (G.encodeLabeling a) e.1 (t e)) ↔
        t = fun e => a e.1 := by
    simp only [matches_encode, funext_iff]
  rw [Finset.sum_eq_single (fun e : G.Incident v => a e.1)]
  · exact ite_eq_left ((matchRow _).mpr rfl)
  · intro t _ hne
    exact ite_eq_right (fun h => hne ((matchRow t).mp h))
  · simp

private theorem witness_uncoded (y : G.Witness q → Bool)
    (outside : y ∉ Set.range (G.encodeLabeling (q:=q))) :
    witnessValue y (G.witnessPolynomial F q) = 0 := by
  classical
  have invalid : ∃ e : G.E, ¬ ∃ a, G.Matches y e a := by
    by_contra! valid
    choose a ha using valid
    apply outside
    refine ⟨a,?_⟩
    funext x
    exact (ha x.1 x.2).symm
  obtain ⟨e,invalidEdge⟩ := invalid
  rw [witnessPolynomial, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (G.left e))
  rw [eval_tablePolynomial]
  apply Finset.sum_eq_zero
  intro t _
  apply ite_eq_right
  intro valid
  let i : G.Incident (G.left e) := ⟨e,Or.inl rfl⟩
  exact invalidEdge ⟨t i,valid i⟩

/-- One Boolean witness contributes each edge-label monomial. For every other
bit string the table factor at an endpoint of an incorrectly encoded edge vanishes. -/
theorem contraction_eq_sum_witness (q : ℕ) :
    G.contraction F q = ∑ y : G.Witness q → Bool, witnessValue y (G.witnessPolynomial F q) := by
  classical
  let code : (G.E → Fin q) ↪ (G.Witness q → Bool) :=
    ⟨G.encodeLabeling, G.encodeLabeling_injective⟩
  let eval (y : G.Witness q → Bool) := witnessValue y (G.witnessPolynomial F q)
  calc
    G.contraction F q = ∑ a, eval (code a) := by
      unfold contraction
      apply Finset.sum_congr rfl
      intro a _
      exact (G.witness_encoded F a).symm
    _ = ∑ y ∈ Finset.univ.map code, eval y := (Finset.sum_map _ code eval).symm
    _ = ∑ y, eval y := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      apply G.witness_uncoded F y
      rintro ⟨a,rfl⟩
      exact hy (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩)


end Hierarchy.IncidenceGraph

end OAI
