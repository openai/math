import OAI.Hierarchy.GraphMonomials
import OAI.Computability.VPVNP.PolynomialBounds
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI
/-! # Arity and degree of a bounded-degree graph contraction family -/

namespace Hierarchy

open Computability.VPVNP

theorem IncidenceGraph.card_tableVar (G : IncidenceGraph) (q : ℕ) :
    Fintype.card (G.TableVar q) = ∑ v : G.V, q ^ G.degree v := by
  classical
  calc
    Fintype.card (G.TableVar q) = Nat.card (G.TableVar q) := Nat.card_eq_fintype_card.symm
    _ = ∑ v : G.V, q ^ G.degree v := by
      unfold IncidenceGraph.TableVar
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro v _
      change Nat.card (G.Incident v → Fin q) = q ^ Fintype.card (G.Incident v)
      rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card]

theorem IncidenceGraph.card_tableVar_le (G : IncidenceGraph) {q b : ℕ} (hq : 0 < q)
    (h : ∀ v, G.degree v ≤ b) :
    Fintype.card (G.TableVar q) ≤ Fintype.card G.V * q ^ b := by
  classical
  calc
    Fintype.card (G.TableVar q) = ∑ v : G.V, q ^ G.degree v := G.card_tableVar q
    _ ≤ ∑ _v : G.V, q ^ b := Finset.sum_le_sum (fun v _ => Nat.pow_le_pow_right hq (h v))
    _ = Fintype.card G.V * q ^ b := by simp

theorem contractionFamily_pFamily (F : Type*) [Field F] (G : ℕ → IncidenceGraph)
    (poly : PolynomiallyBounded (fun n => Fintype.card (G n).V))
    (deg : ∃ b, ∀ n (v : (G n).V), (G n).degree v ≤ b) :
    PFamily (contractionFamily F G) := by
  obtain ⟨b, hb⟩ := deg
  constructor
  · apply (poly.mul (PolynomiallyBounded.id.pow b)).of_eventually_le 1
    intro n hn
    exact (G n).card_tableVar_le hn (hb n)
  · apply poly.of_eventually_le 1
    intro n hn
    exact ((G n).totalDegree_contraction F (fun _ => ⟨0, hn⟩)).le

end Hierarchy

end OAI
