import OAI.Computability.VPVNP.RankQueryDescribeSpace

/-! # A common polynomial allowance for the descriptor's own work

The Macaulay callback contributes its clock twice and its peak stack height
once. All remaining time and storage have a fixed quartic majorant in the
register width, field limb width, and extension degree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.DescribeAdapter

open Dispatch

/-- One hundred times the number of instructions emitted for the six output fields of `op`.
Multiplication by `(w+1)^2` gives its word-operation clock. -/
def codeCost (op : Operation) := (op.tree.emitFields capacity (List.finRange 6)).length * 100

private theorem opClock (op : Operation) (w : ℕ) : op.clock w = codeCost op * (w+1)^2 := by
  unfold Operation.clock codeCost
  rw [Nat.mul_assoc]

/-- Quartic bound on the descriptor's own time and stack growth when register width, limb width
and extension degree are all at most `x`. -/
def allowance (x : ℕ) := (codeCost .describe + codeCost .gram + 4000)*(x+1)^4

theorem clock_eq (w v e B : ℕ) : clock w v e B = 2*B+clock w v e 0 := by
  unfold clock timeWith GramScalar.clock; omega

theorem space_le_clock (w v e A S : ℕ) : space w v e A S ≤ max A S + clock w v e 0 := by
  unfold space peakWith clock timeWith GramScalar.space GramScalar.clock
  dsimp only
  have h : max (A+Operation.describe.clock w+Operation.gram.clock w) S ≤
      max A S + Operation.describe.clock w + Operation.gram.clock w := max_le (by omega) (by omega)
  omega

private theorem addCap_le (e v x : ℕ) (he : e ≤ x) (hv : v ≤ x) :
    SliceArithmetic.AddCall.callCap e v ≤ 500*(x+1)^4 := by
  calc
    _ ≤ SliceArithmetic.AddCall.callCap x x := by unfold SliceArithmetic.AddCall.callCap; gcongr
    _ ≤ _ := by unfold SliceArithmetic.AddCall.callCap; ring_nf; omega

theorem overhead_le (w v e x : ℕ) (hw : w ≤ x) (hv : v ≤ x) (he : e ≤ x) :
    clock w v e 0 ≤ allowance x := by
  have hm : SliceArithmetic.MultiplyCall.callCap e v ≤ 2000*(x+1)^4 := calc
    _ ≤ 2000*(e+1)^2*(v+1)^2 := SliceArithmetic.MultiplyCall.callCap_le e v
    _ ≤ 2000*(x+1)^2*(x+1)^2 := by gcongr
    _ = _ := by ring
  have ha := addCap_le e v x he hv
  have hc₁ : Operation.describe.clock w ≤ codeCost .describe*(x+1)^2 := by rw [opClock]; gcongr
  have hc₂ : Operation.gram.clock w ≤ codeCost .gram*(x+1)^2 := by rw [opClock]; gcongr
  have hv' := Nat.mul_le_mul he hv
  unfold clock timeWith GramScalar.clock allowance
  generalize h₁ : codeCost .describe = a at *
  generalize h₂ : codeCost .gram = b at *
  ring_nf at hv' hc₁ hc₂ hm ha ⊢
  omega

/-- Read the local clock and space bounds directly from the compact inputs. -/
theorem clock_space_le (w v e x B A S : ℕ) (hw : w ≤ x) (hv : v ≤ x) (he : e ≤ x) :
    clock w v e B ≤ 2*B + allowance x ∧ space w v e A S ≤ max A S + allowance x := by
  have h := overhead_le w v e x hw hv he
  exact ⟨(clock_eq ..).le.trans (Nat.add_le_add_left h _),
    (space_le_clock ..).trans (Nat.add_le_add_left h _)⟩

end RankQuery.Stack.DescribeAdapter

end VPVNP
end Computability
end OAI
