import OAI.Hierarchy.GraphVNPPolynomial
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Number of Boolean labels in the one-hot graph verifier -/

namespace Hierarchy.IncidenceGraph

theorem card_edges_le (G : IncidenceGraph) {b : ℕ} (deg : ∀ v, G.degree v ≤ b) :
    Fintype.card G.E ≤ Fintype.card G.V * b := by
  classical
  let atLeft (e : G.E) : (v : G.V) × G.Incident v := ⟨G.left e, e, Or.inl rfl⟩
  have inj : Function.Injective atLeft := by
    intro e f h
    exact congrArg (fun p : (v : G.V) × G.Incident v => p.2.val) h
  calc
    Fintype.card G.E ≤ Fintype.card ((v : G.V) × G.Incident v) :=
      Fintype.card_le_of_injective atLeft inj
    _ = ∑ v : G.V, G.degree v := Fintype.card_sigma
    _ ≤ ∑ _v : G.V, b := Finset.sum_le_sum (fun v _ => deg v)
    _ = Fintype.card G.V * b := by simp

theorem card_witness_le (G : IncidenceGraph) (q : ℕ) {b : ℕ} (deg : ∀ v, G.degree v ≤ b) :
    Fintype.card (G.Witness q) ≤ Fintype.card G.V * b * q := by
  simpa only [Witness, Fintype.card_prod, Fintype.card_fin] using
    Nat.mul_le_mul_right q (G.card_edges_le deg)

end Hierarchy.IncidenceGraph

end OAI
