import OAI.ThreeFlat.Concentrator.Peeling
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum

namespace OAI
/-! # The public bipartite graph of the two-pass concentrator

A left vertex may use one of its listed greedy candidates or any reserve
slot at one of its two endpoints. Both banks embed in the advertised right
slot set. Unused public slots have no incident edges.
-/

namespace ThreeFlat.Concentrator

variable {L A V : Type*} {slots R : ℕ} [DecidableEq A] [DecidableEq V]
variable (e : A ⊕ (V × Fin slots) ↪ Fin R) (N : L → List A) (G : ReserveGraph L V)

/-- The public candidate slots, independent of the active mask. -/
def publicNeighbors (x : L) : Finset (Fin R) :=
  ((N x).toFinset.disjSum
    (({G.src x, G.dst x} : Finset V).product (Finset.univ : Finset (Fin slots)))).map e

theorem mem_publicNeighbors_iff (x : L) (z : A ⊕ (V × Fin slots)) :
    e z ∈ publicNeighbors e N G x ↔
      match z with
      | .inl a => a ∈ N x
      | .inr (v, _) => v = G.src x ∨ v = G.dst x := by
  cases z with
  | inl a => simp [publicNeighbors]
  | inr z => rcases z with ⟨v, i⟩; simp [publicNeighbors]

theorem mem_publicNeighbors_of_adjacent (x : L) (z : A ⊕ (V × Fin slots))
    (hadj : match z with
      | .inl a => a ∈ N x
      | .inr (v, _) => v = G.src x ∨ v = G.dst x) : e z ∈ publicNeighbors e N G x :=
  (mem_publicNeighbors_iff e N G x z).mpr hadj

theorem publicNeighbors_left_degree {degree : ℕ}
    (length_le : ∀ x, (N x).length ≤ degree) (x : L) :
    (publicNeighbors e N G x).card ≤ degree + 2 * slots := by
  simp only [publicNeighbors, Finset.card_map, Finset.card_disjSum]
  apply Nat.add_le_add ((N x).toFinset_card_le.trans (length_le x))
  calc
    _ = ({G.src x, G.dst x} : Finset V).card * (Finset.univ : Finset (Fin slots)).card :=
      Finset.card_product _ _
    _ ≤ 2 * slots := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_le_mul_right slots Finset.card_le_two

theorem publicNeighbors_right_degree [Fintype L] {degree reserveDegree : ℕ}
    (contenders : ∀ a, (Finset.univ.filter fun x => a ∈ N x).card ≤ degree)
    (incidences : ∀ v, (G.incident Finset.univ v).card ≤ reserveDegree) (r : Fin R) :
    (Finset.univ.filter fun x => r ∈ publicNeighbors e N G x).card ≤ max degree reserveDegree := by
  by_cases filled : ∃ z, e z = r
  · obtain ⟨a | ⟨v, i⟩, rfl⟩ := filled
    · have eq : (Finset.univ.filter fun x => e (.inl a) ∈ publicNeighbors e N G x) =
          (Finset.univ.filter fun x => a ∈ N x) := by
        ext x
        simp [mem_publicNeighbors_iff]
      rw [eq]
      exact (contenders a).trans (le_max_left _ _)
    · have eq : (Finset.univ.filter fun x => e (.inr (v,i)) ∈ publicNeighbors e N G x) =
          G.incident Finset.univ v := by
        ext x
        simp [mem_publicNeighbors_iff, ReserveGraph.incident, eq_comm]
      rw [eq]
      exact (incidences v).trans (le_max_right _ _)
  · have empty : (Finset.univ.filter fun x => r ∈ publicNeighbors e N G x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨z, _, hz⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hx).2
      exact filled ⟨z, hz⟩
    simp [empty]

end ThreeFlat.Concentrator

end OAI
