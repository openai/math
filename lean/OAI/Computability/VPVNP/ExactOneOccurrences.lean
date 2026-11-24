import OAI.Computability.VPVNP.ExactOneFirst
import OAI.Computability.VPVNP.ExactOneSize

/-!
# Flattening exact-one literal occurrences for the graph reductions

The graph for Hamiltonian cycles and the graph for cycle covers have one indexed
occurrence per literal position. Each occurrence retains its variable, clause,
and polarity. Multiple occurrences of the same literal stay distinct.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF

variable {k : ℕ}

theorem card_occ (φ : CNF k) : Fintype.card (Occ φ) = literalCount φ := by
  simp only [Occ, Fintype.card_sigma, Fintype.card_fin, sum_lengths]

/-- The graph may number occurrences by any bijection. -/
noncomputable def occurrenceIndex (φ : CNF k) : Fin (literalCount φ) ≃ Occ φ :=
  (Fintype.equivFinOfCardEq (card_occ φ)).symm

/-- The variable, clause and satisfying bit of occurrence `j`. -/
noncomputable def occurrences (φ : CNF k) (j : Fin (literalCount φ)) :
    Fin k × Fin φ.length × Bool :=
  let z := occurrenceIndex φ j
  let lit := φ[z.1][z.2]
  (lit.1, z.1, lit.2)

private theorem countP_eq_one_iff_position {A : Type*} (c : List A) (f : A → Bool) :
    c.countP f = 1 ↔ ∃! j : Fin c.length, f c[j] = true := by
  have hc : (List.finRange c.length).map (fun i : Fin c.length => c[i]) = c := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem
  have h := countP_finRange_eq_one (fun i : Fin c.length => f c[i])
  have eqCount := congrArg (List.countP f) hc
  rw [List.countP_map] at eqCount
  rw [← eqCount]
  exact h

private theorem existsUnique_occ_iff (φ : CNF k) (x : Fin k → Bool) (a : Fin φ.length) :
    (∃! z : Occ φ, z.1 = a ∧ x (φ[z.1][z.2]).1 = (φ[z.1][z.2]).2) ↔
      ∃! i : Fin φ[a].length, x (φ[a][i]).1 = (φ[a][i]).2 := by
  constructor
  · rintro ⟨⟨c, i⟩, ⟨rfl, hi⟩, hu⟩
    refine ⟨i, hi, fun j hj => ?_⟩
    exact eq_of_heq (Sigma.mk.inj_iff.mp (hu ⟨c, j⟩ ⟨rfl, hj⟩)).2
  · rintro ⟨i, hi, hu⟩
    refine ⟨⟨a, i⟩, ⟨rfl, hi⟩, ?_⟩
    rintro ⟨c, j⟩ ⟨rfl, hj⟩
    exact congrArg (Sigma.mk c) (hu j hj)

/-- Exact-one satisfaction is equivalent to one true numbered occurrence in each clause. -/
theorem holds_iff_unique_occurrence (φ : CNF k) (x : Fin k → Bool) :
    Holds φ x ↔ ∀ a : Fin φ.length, ∃! j : Fin (literalCount φ),
      (occurrences φ j).2.1 = a ∧ x (occurrences φ j).1 = (occurrences φ j).2.2 := by
  simp only [Holds, List.forall_mem_iff_get]
  apply forall_congr'
  intro a
  rw [countP_eq_one_iff_position]
  simp only [beq_iff_eq]
  exact (existsUnique_occ_iff φ x a).symm.trans
    (occurrenceIndex φ).existsUnique_congr_right.symm

/-- Any family member containing an empty clause has zero satisfying assignments. -/
theorem not_holds_of_nil_mem {φ : CNF k} (h : [] ∈ φ) (x : Fin k → Bool) : ¬ Holds φ x := by
  intro hx
  simpa using hx [] h

/-- Without empty clauses the graph's number of clause vertices is at most the literal count. -/
theorem length_le_literalCount_of_nil_notMem {φ : CNF k} (h : [] ∉ φ) :
    φ.length ≤ literalCount φ := by
  rw [← sum_lengths]
  have hpos (c : Fin φ.length) : 1 ≤ φ[c].length := by
    have hc : φ[c] ≠ [] := fun he => h (he ▸ List.getElem_mem _)
    exact List.length_pos_iff.mpr hc
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpos c)

end ExactOne

end VPVNP
end Computability
end OAI
