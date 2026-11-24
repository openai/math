import OAI.Computability.VPVNP.ExactOneOccurrences
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Clause choices in the cycle-cover reduction

In an exact-one assignment each clause has a unique chosen occurrence. Conversely,
matching all chosen occurrences against the active arcs of the variable rings forces
that assignment to satisfy the exact-one conditions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open HardnessCNF ExactOne

variable {k m c : ℕ}

/-- Each clause chooses an occurrence which belongs to it. -/
def ownerOK (occ : Fin m → Fin k × Fin c × Bool) (y : Fin c → Fin m) : Prop :=
  ∀ a, (occ (y a)).2.1 = a

/-- The occurrence numbered `j` is the choice of its clause. -/
def selected (occ : Fin m → Fin k × Fin c × Bool) (y : Fin c → Fin m) (j : Fin m) : Prop :=
  y (occ j).2.1 = j

private def compatible (occ : Fin m → Fin k × Fin c × Bool)
    (x : Fin k → Bool) (y : Fin c → Fin m) : Prop :=
  ownerOK occ y ∧ ∀ j, selected occ y j ↔ x (occ j).1 = (occ j).2.2

private theorem unique_in_clause (occ : Fin m → Fin k × Fin c × Bool)
    (x : Fin k → Bool) (y : Fin c → Fin m) (hy : compatible occ x y) (a : Fin c) :
    ∃! j, (occ j).2.1 = a ∧ x (occ j).1 = (occ j).2.2 := by
  refine ⟨y a, ⟨hy.1 a, (hy.2 _).mp ?_⟩, ?_⟩
  · exact congrArg y (hy.1 a)
  · rintro j ⟨hj, h⟩
    have hs := (hy.2 j).mpr h
    simpa [selected, hj] using hs.symm

private theorem unique_selection (occ : Fin m → Fin k × Fin c × Bool)
    (x : Fin k → Bool)
    (h : ∀ a, ∃! j, (occ j).2.1 = a ∧ x (occ j).1 = (occ j).2.2) :
    ∃! y, compatible occ x y := by
  classical
  choose y hy hu using h
  have hcomp : compatible occ x y := by
    refine ⟨fun a => (hy a).1, fun j => ?_⟩
    constructor
    · intro hj
      have ha := (hy (occ j).2.1).2
      rwa [hj] at ha
    · intro hj
      exact (hu (occ j).2.1 j ⟨rfl, hj⟩).symm
  refine ⟨y, hcomp, ?_⟩
  intro z hz
  funext a
  apply hu a (z a)
  exact ⟨hz.1 a, (hz.2 _).mp (congrArg z (hz.1 a))⟩

open scoped Classical in
/-- The clause selector contributes precisely one copy of a compatible weight. -/
theorem sum_clause_choices {R : Type*} [CommSemiring R]
    (φ : CNF k) (x : Fin k → Bool) (weight : R) :
    (∑ y : Fin φ.length → Fin (literalCount φ),
      if (∀ a, (occurrences φ (y a)).2.1 = a) ∧
          (∀ j, y (occurrences φ j).2.1 = j ↔ x (occurrences φ j).1 = (occurrences φ j).2.2)
      then weight else 0) = if Holds φ x then weight else 0 := by
  classical
  trans (∑ y, if compatible (occurrences φ) x y then weight else 0)
  · apply Finset.sum_congr rfl
    intro y _
    by_cases hy : compatible (occurrences φ) x y <;>
      simp only [compatible, ownerOK, selected] at hy ⊢ <;> simp [hy]
  by_cases h : Holds φ x
  · obtain ⟨y, hy, hu⟩ := unique_selection (occurrences φ) x ((holds_iff_unique_occurrence φ x).mp h)
    have eq_choice (z : Fin φ.length → Fin (literalCount φ)) :
        compatible (occurrences φ) x z ↔ z = y := ⟨hu z, fun hz => hz ▸ hy⟩
    simp [eq_choice, h]
  · have no_choice (y : Fin φ.length → Fin (literalCount φ)) :
        ¬ compatible (occurrences φ) x y := fun hy =>
      h ((holds_iff_unique_occurrence φ x).mpr (unique_in_clause _ _ y hy))
    simp [no_choice, h]

end PermanentReduction

end VPVNP
end Computability
end OAI
