import OAI.Computability.VPVNP.HardnessQuery

/-! # Reindexing weighted exact-one incidence tables

A table may label its rows and columns by arbitrary finite types. Enumerating
both types by finite ordinals preserves both the unique-column test and every
selected variable or scalar factor in the polynomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace IncidenceMachine

open MvPolynomial
open scoped Classical

/-- Boolean test that each row is incident with exactly one of the selected columns. -/
noncomputable def exactOne {U V : Type*} (M : U → V → Bool) (x : V → Bool) : Bool :=
  decide (∀ r, ∃! i, x i = true ∧ M r i = true)

theorem weighted_exactOne_reindex {U V τ R : Type*} [Fintype U] [Fintype V] [CommRing R]
    {m k : ℕ} (rows : Fin m ≃ U) (cols : Fin k ≃ V)
    (M : U → V → Bool) (w : V → τ ⊕ R) :
    weightedPredicate (exactOne (fun r i => M (rows r) (cols i))) (w ∘ cols) =
      ∑ x : V → Bool, if ∀ r, ∃! i, x i = true ∧ M r i = true then
        ∏ i, if x i then (w i).elim X C else 1 else 0 := by
  let e : (V → Bool) ≃ (Fin k → Bool) := cols.symm.arrowCongr (Equiv.refl Bool)
  rw [weightedPredicate, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change (if exactOne (fun r i => M (rows r) (cols i)) (fun i => x (cols i)) then
    ∏ i, if x (cols i) then (w (cols i)).elim X C else 1 else 0) = _
  have hp (r : U) : (∃! i : Fin k, x (cols i) = true ∧ M r (cols i) = true) ↔
      ∃! j : V, x j = true ∧ M r j = true :=
    cols.existsUnique_congr_right (q := fun j => x j = true ∧ M r j = true)
  have hr : (∀ r : Fin m, ∃! j : V, x j = true ∧ M (rows r) j = true) ↔
      ∀ r : U, ∃! j : V, x j = true ∧ M r j = true :=
    rows.forall_congr_right (q := fun r => ∃! j : V, x j = true ∧ M r j = true)
  simp only [exactOne, decide_eq_true_eq, hp, hr,
    cols.prod_comp (fun i => if x i then (w i).elim X C else 1)]

end IncidenceMachine

end VPVNP
end Computability
end OAI
