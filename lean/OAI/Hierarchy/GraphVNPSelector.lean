import OAI.Hierarchy.GraphVNPPolynomial
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI
/-! # Boolean evaluation of the local edge selectors -/

namespace Hierarchy.IncidenceGraph

open MvPolynomial
open scoped Classical BigOperators

variable (G : IncidenceGraph)

/-- The bits on this edge give exactly the one-hot code of the label. -/
def Matches {q : ℕ} (y : G.Witness q → Bool) (e : G.E) (a : Fin q) : Prop :=
  ∀ i, y (e,i) = decide (i=a)

theorem Matches.unique {q : ℕ} {y : G.Witness q → Bool} {e : G.E} {a b : Fin q}
    (ha : G.Matches y e a) (hb : G.Matches y e b) : a=b := by
  apply of_decide_eq_true
  simpa using (hb a).symm.trans (ha a)

variable (F : Type*) [Field F] (q : ℕ) (y : G.Witness q → Bool)

private theorem eval_labelFactor (e : G.E) (a i : Fin q) :
    Computability.VPVNP.witnessValue y (G.labelFactor F q e a i) =
      if y (e,i) = decide (i=a) then 1 else 0 := by
  by_cases hit : i=a
  · subst i
    cases bit : y (e,a) <;> simp [labelFactor, Computability.VPVNP.witnessValue, bit]
  · rw [labelFactor, ite_eq_right hit, map_sub, map_one]
    cases bit : y (e,i) <;> simp [Computability.VPVNP.witnessValue, hit, bit]

theorem eval_labelSelector (e : G.E) (a : Fin q) :
    Computability.VPVNP.witnessValue y (G.labelSelector F q e a) =
      if G.Matches y e a then 1 else 0 := by
  by_cases hit : G.Matches y e a
  · rw [ite_eq_left hit, labelSelector, map_prod]
    apply Finset.prod_eq_one
    intro i _
    rw [G.eval_labelFactor F q y, ite_eq_left (hit i)]
  · rw [ite_eq_right hit, labelSelector, map_prod]
    obtain ⟨i,bad⟩ := not_forall.mp hit
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [G.eval_labelFactor F q y, ite_eq_right bad])

private theorem eval_tableTerm (v : G.V) (t : G.Incident v → Fin q) :
    Computability.VPVNP.witnessValue y (G.tableTerm F q v t) =
      if ∀ e : G.Incident v, G.Matches y e.val (t e) then X ⟨v,t⟩ else 0 := by
  have visible : Computability.VPVNP.witnessValue (F:=F) y (X (Sum.inl (⟨v,t⟩ : G.TableVar q))) = X ⟨v,t⟩ := by
    simp [Computability.VPVNP.witnessValue]
  simp only [tableTerm, map_mul, map_prod, visible, G.eval_labelSelector F q y, Fintype.prod_boole]
  split <;> simp_all

/-- Only the local assignments whose incident-edge bits all match survive. -/
theorem eval_tablePolynomial (v : G.V) :
    Computability.VPVNP.witnessValue y (G.tablePolynomial F q v) =
      ∑ t : G.Incident v → Fin q,
        if ∀ e : G.Incident v, G.Matches y e.val (t e) then X ⟨v,t⟩ else 0 := by
  simp only [tablePolynomial, map_sum, G.eval_tableTerm F q y]

end Hierarchy.IncidenceGraph

end OAI
