import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryPrefix

/-! # Unconditional elementary routing of a Walsh column XOR

One two-bit lookup is applied for each position of the aligned slot pair.
The machine and its cut schedule are uniform in the node depth, both spectator
dimensions and the record width. Every pass reuses the same physical arena.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.ElementarySweep

open IntegerMultiplication Code Space PhysicalWalsh
open ElementarySchedule (slotWidth)

/-- The fallback clock pays one pass per bit of a slot on the actual record volume. -/
def extra (A : ℕ) := prefixExtra A (slotWidth A)

/-- A common degree covers every directed pair of columns in a fixed template.
The scan and arena budgets are those consumed by the recursive machine. -/
theorem flatRuns (a W : ℕ) : ∃ D : ℕ, ∀ d, D ≤ d →
    FlatXorRuns a W (nodeScan a W d (extra (a+1))) (nodeArena a W d) := by
  obtain ⟨D,partialGate⟩ := prefixRun a W (slotWidth (a+1)) (Header.childBits _ (Nat.succ_pos _)) (fun _ => le_rfl)
  refine ⟨D,fun d hd g ne => ?_⟩
  have gate := partialGate d hd g.2 g.1 ne.symm
  apply gate.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  intro t
  apply congrArg (fun f => send (laneFlat (a+1) W t.shape f))
  funext n
  exact congrArg t.row (address_full g.2 g.1 ne.symm t.shape n)

/-- The elementary router is available on every admitted node and every data row. -/
theorem xorRuns (a W : ℕ) : ∃ D : ℕ, ∀ d, D ≤ d →
    XorRuns a W (nodeScan a W d (extra (a+1))) (nodeArena a W d) := by
  obtain ⟨D,h⟩ := flatRuns a W
  exact ⟨D,fun d hd => xorRuns_of_flat (fun _ => Nat.le_add_right ..) (fun _ => le_max_right ..) (h d hd)⟩

end PhysicalWalshNode.ElementarySweep

end NearSquareRoot
end Computability
end OAI
