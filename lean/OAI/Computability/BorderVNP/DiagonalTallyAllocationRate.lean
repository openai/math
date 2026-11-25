import OAI.Computability.BorderVNP.DiagonalTallyAlign

/-! # Polynomial address room for length-only residue query pointers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyAllocation

/-- One-past-last query bit produced for any legal count in the indicated dimensions. -/
def AfterTasks.endAddress (a : AfterTasks) (dim teams w : ℕ) :=
  a.localBase+dim+teams*dim+dim+dim+1+dim*w

/-- A fixed polynomial controls the entire post-task region including the right-aligned
sparse record bank, common subtotal arrays and all serialized Fourier query words. -/
theorem AfterTasks.endAddress_le (a : AfterTasks) {K dim teams w : ℕ}
    (hb : a.bound.Le K) (hd : dim ≤ 2*K) (ht : teams ≤ K) (hw : w ≤ K) :
    a.endAddress dim teams w ≤ a.start+64*(K+1)^3 := by
  have b := a.polynomial_room hb
  have td := Nat.mul_le_mul ht hd
  have dw := Nat.mul_le_mul hd hw
  have cg := Nat.mul_le_mul hb.cells hb.gadgets
  unfold endAddress localBase Bounds.operands
  nlinarith [hb.uses,hb.vertices]

/-- The allocation formulas separate the live geometry sources and the complete
per-cell counter, row and header banks from the later typed task windows. -/
theorem BeforeTasks.ordered (a : BeforeTasks) :
    a.tailWidths+a.bound.cells ≤ a.supplement ∧
    a.supplement+a.bound.cells*a.bound.supplementStride ≤ a.counters ∧
    a.counters+2*a.bound.cells ≤ a.merged ∧ a.merged+a.bound.cells ≤ a.four ∧
    a.four+4*a.bound.cells ≤ a.six ∧ a.six+6*a.bound.cells ≤ a.ranges ∧
    a.ranges+2*a.bound.cells ≤ a.bundleTable ∧ a.bundleTable+6*a.bound.bundles ≤ a.limit := by
  exact ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩

end DiagonalTallyAllocation

end BorderVNP
end Computability
end OAI
