import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPrune
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

/-! # The table entries of a trivalent patch

Each entry has an address identifying its vertex and the values at the three
incident ports. A common dimension bound gives at most its cube per vertex.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V K : Type*} {d : V → ℕ}

namespace TrivalentTree

/-- Addresses of scalar table entries at the internal vertices. -/
def Entry : {q : ℕ} → TrivalentTree K d q → Type
  | _, .port _ => Empty
  | q, .branch (i := i) (j := j) _ t u =>
    (Fin q × Fin i × Fin j) ⊕ (Entry t ⊕ Entry u)

instance instFintypeEntry : {q : ℕ} → (t : TrivalentTree K d q) → Fintype t.Entry
  | _, .port _ => inferInstanceAs (Fintype Empty)
  | q, .branch (i := i) (j := j) _ t u => by
    letI := instFintypeEntry t
    letI := instFintypeEntry u
    exact inferInstanceAs (Fintype ((Fin q × Fin i × Fin j) ⊕ (Entry t ⊕ Entry u)))

/-- Read the three-index table at a given address. -/
def entry : {q : ℕ} → (t : TrivalentTree K d q) → t.Entry → K
  | _, .port _ => Empty.elim
  | _, .branch B t u => Sum.elim (fun p ↦ B p.1 p.2.1 p.2.2) (Sum.elim t.entry u.entry)

theorem output_bounded {q D : ℕ} (t : TrivalentTree K d q) (h : t.Bounded D) : q ≤ D := by
  cases t with
  | port => exact h
  | branch => exact h.1

/-- A uniform cost estimate for enumerating all entries is cubic in the
maximum bond dimension, irrespective of the shape of the tree. -/
theorem card_entry_le {q D : ℕ} (t : TrivalentTree K d q) (h : t.Bounded D) :
    Fintype.card t.Entry ≤ t.vertices * D ^ 3 := by
  induction t with
  | port =>
    change @Fintype.card Empty _ ≤ 0 * D ^ 3
    rw [Fintype.card_of_isEmpty, Nat.zero_mul]
  | @branch q i j B t u ih jh =>
    obtain ⟨hq, ht, hu⟩ := h
    have hroot := Nat.mul_le_mul hq (Nat.mul_le_mul (t.output_bounded ht) (u.output_bounded hu))
    change Fintype.card ((Fin q × Fin i × Fin j) ⊕ (t.Entry ⊕ u.Entry)) ≤ _
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, vertices, Nat.add_mul,
      one_mul]
    have hc : q * (i * j) ≤ D ^ 3 := by simpa [pow_succ, Nat.mul_assoc] using hroot
    have hl := ih ht
    have hr := jh hu
    omega

end TrivalentTree

namespace OrderedTensorTree

/-- The number of contraction levels bounds the number of successive
coefficient-table operations on any path in the pruning algorithm. -/
def height : {q : ℕ} → OrderedTensorTree K d q → ℕ
  | _, .scalar _ | _, .stub _ _ => 0
  | _, .unary _ t => t.height + 1
  | _, .branch _ t u => max t.height u.height + 1

end OrderedTensorTree

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
