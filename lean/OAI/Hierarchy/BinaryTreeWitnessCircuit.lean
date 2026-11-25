import OAI.Hierarchy.BinaryTreeMessages
import OAI.Hierarchy.BinaryTreeCircuitRows
import OAI.Hierarchy.BinaryTreeWitnessSize
import OAI.Hierarchy.GraphFamilyBounds

namespace OAI
/-! # Polynomial-size circuits for the complete binary tree contractions

Every subtree computes one common table of outputs for all values of its incoming edge.
Combining two such tables takes at most three arithmetic gates per triple of edge colors.
-/

namespace Hierarchy.BinaryTree
open Computability.VPVNP MvPolynomial
open scoped BigOperators
noncomputable section

/-- A single forward program holds all the messages at the root of the given subtree. -/
theorem MessageTree.program (F : Type*) [Field F] {σ : Type} {q h : ℕ}
    (t : MessageTree σ q h) :
    ∃ n ≤ (3 * q^3) * Fintype.card (V h), ∃ (p : Program F σ n) (result : Fin q → Ref F σ n),
      ∀ a, (Circuit.mk p (result a)).polynomial = t.eval F a := by
  classical
  induction t with
  | leaf label =>
    exact ⟨0, Nat.zero_le _, .nil, fun a => .var (label a), fun _ => rfl⟩
  | @fork h label l r leftIH rightIH =>
    obtain ⟨nl, bl, pl, left, hl⟩ := leftIH
    obtain ⟨nr, br, pr, right, hr⟩ := rightIH
    obtain ⟨left', right', keepL, keepR⟩ := joinTables pl pr left right
    obtain ⟨n, bn, p, ref, reads⟩ := extendMessages (pl.append pr) left' right' label
    refine ⟨n, ?_, p, ref, ?_⟩
    · rw [card_succ]
      calc
        n ≤ (nl+nr) + 3*q^3 := bn
        _ ≤ ((3*q^3)*Fintype.card (V h) + (3*q^3)*Fintype.card (V h)) + 3*q^3 :=
          Nat.add_le_add_right (Nat.add_le_add bl br) _
        _ = _ := by ring
    · intro a
      simpa only [MessageTree.eval,keepL,keepR,hl,hr] using reads a

/-- The independent-table polynomial of the whole height-`h` tree uses at most
`3*q³` gates per vertex. The root uses no additional edge label. -/
theorem circuitSize_contraction (F : Type*) [Field F] (h q : ℕ) (hq : 0 < q) :
    circuitSize ((graph h).contraction F q) ≤ (3*q^3)*Fintype.card (V h) := by
  obtain ⟨tree, color, computes⟩ := realizes_contraction F h q hq
  obtain ⟨n, price, p, ref, values⟩ := tree.program F
  exact circuitSize_le_iff.mpr
    ⟨n, price, ⟨p, ref color⟩, (values color).trans computes⟩

/-- At index `n` the tree has height `⌊log₂ n⌋` and edge alphabet `Fin n`. -/
theorem isVP (F : Type*) [Field F] :
    Computability.VPVNP.IsVP (contractionFamily F (fun n => graph (Nat.log 2 n))) := by
  have order := log_order_polynomial
  refine ⟨contractionFamily_pFamily F _ order ⟨3, fun n v => degree_le_three _ v⟩, ?_⟩
  have gateBound := ((PolynomiallyBounded.const 3).mul (PolynomiallyBounded.id.pow 3)).mul order
  apply gateBound.of_eventually_le 1
  intro n hn
  exact circuitSize_contraction F (Nat.log 2 n) n hn


end
end Hierarchy.BinaryTree

end OAI
