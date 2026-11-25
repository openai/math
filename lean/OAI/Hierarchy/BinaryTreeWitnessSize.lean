import OAI.Hierarchy.BinaryTree
import OAI.Computability.VPVNP.PolynomialBounds
import Mathlib.Data.Nat.Log

namespace OAI
/-! # A binary-tree witness family of polynomial order -/

namespace Hierarchy.BinaryTree

/-- Indexing the complete binary trees by logarithmic height gives polynomial vertex count. -/
theorem log_order_polynomial :
    Computability.VPVNP.PolynomiallyBounded (fun n => Fintype.card (graph (Nat.log 2 n)).V) := by
  refine ⟨2, 1, 1, fun n hn => ?_⟩
  change Fintype.card (V (Nat.log 2 n)) ≤ 2 * n ^ 1
  rw [pow_one]
  have size := card_vertices (Nat.log 2 n)
  rw [pow_succ] at size
  have bound := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  omega


end Hierarchy.BinaryTree

end OAI
