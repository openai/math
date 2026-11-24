import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Products indexed by the selected ports

Each marked ring row can use one input port. A clause row chooses one occurrence in that
clause. Reindexing these products counts the occupied ports once per gadget.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

variable {U G A : Type*} [Fintype U] [Fintype G] [CommMonoid A]

/-- Reindex a product of optional factors by the occupied ports. -/
theorem prod_optional_ports (pick : U → Option G) (pos : G → U) (active : G → Bool)
    (hf : ∀ u g, pick u = some g ↔ u = pos g ∧ active g = true) (w : G → A) :
    (∏ u, (pick u).elim 1 w) = ∏ g, if active g then w g else 1 := by
  classical
  calc
    _ = ∏ u, ∏ g, if pick u = some g then w g else 1 := by
      apply Finset.prod_congr rfl
      intro u _
      cases h : pick u <;> simp
    _ = ∏ g, ∏ u, if u = pos g ∧ active g = true then w g else 1 := by
      simp_rw [hf]
      exact Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro g _
      cases active g <;> simp

/-- Reindex one selected occurrence per clause by the occurrence set. -/
theorem prod_clause_ports [DecidableEq G] (pick : U → G) (owner : G → U)
    (howner : ∀ u, owner (pick u) = u) (w : G → A) :
    (∏ u, w (pick u)) = ∏ g, if pick (owner g) = g then w g else 1 := by
  classical
  have hport (u : U) (g : G) : some (pick u) = some g ↔ u = owner g ∧ decide (pick (owner g) = g) = true := by
    simp only [Option.some.injEq, decide_eq_true_eq]
    constructor
    · rintro rfl
      simp [howner]
    · rintro ⟨rfl, h⟩
      exact h
  simpa using prod_optional_ports (fun u => some (pick u)) owner
    (fun g => decide (pick (owner g) = g)) hport w

end PermanentReduction

end VPVNP
end Computability
end OAI
