import OAI.Computability.VPVNP.HardnessWeights
import OAI.Computability.VPVNP.ParseEventWeights
import OAI.Computability.VPVNP.ParseTreeBits

/-! # Weighted CNF for a grammar state

The incidence clauses select one Boolean assignment per ordered parse. The
product of its selected coordinates counts every production scalar and every
terminal variable with the multiplicity of that occurrence in the tree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

open HardnessCNF MvPolynomial
open scoped Classical

variable {R V H : Type*} {D : ℕ}
variable [CommSemiring R] [Fintype V] [Fintype H]

private theorem weightedCNF_eq_sum_subtype {k : ℕ} (φ : CNF k) (w : Fin k → R) :
    weightedCNF φ w = ∑ x : {x // Satisfies φ x}, ∏ i, if x.val i then w i else 1 := by
  rw [weightedCNF, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun x => by simp) _

private theorem prod_selected_events (w : ParseEvent V H → R)
    (x : Fin (Fintype.card (EventCode V H D)) → Bool) :
    ∏ e ∈ EventCode.selected V H D x, w e =
      ∏ i, if x i then w (EventCode.enumerate V H D i) else 1 := by
  rw [EventCode.selected, Finset.prod_image (EventCode.enumerate_injective V H D).injOn,
    Finset.prod_filter]

/-- Reindex the grammar polynomial's parse expansion by satisfying Boolean
assignments to the incidence clauses. -/
theorem eval_eq_weightedCNF (G : ParseGrammar R V H D) (d : Fin D) (h : H) :
    G.eval d h = weightedCNF (incidenceCNF (EventCode.enumerate V H D) 0 d.val h)
      (fun i => C (G.eventScalar (EventCode.enumerate V H D i)) *
        (EventCode.enumerate V H D i).leafValue X) := by
  rw [G.eval_eq_sum_eventWeights d h 0, weightedCNF_eq_sum_subtype,
    ← (EventCode.satisfyingEquiv V H D d h).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [EventCode.events_satisfyingEquiv]
  exact prod_selected_events _ x.val

end ParseGrammar

end VPVNP
end Computability
end OAI
