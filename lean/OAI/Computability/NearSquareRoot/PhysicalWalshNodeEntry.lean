import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSpec
import OAI.Computability.NearSquareRoot.PhysicalWalshPadding

/-! # Dispatching a compact Walsh request

The first tally in the compact descriptor is the remaining recursion level.
Testing whether it is empty supplies the branch taken by the recursive tape
interpreter while preserving the descriptor and every record in the input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.Header

open IntegerMultiplication Code Space

private def dispatch (v : Wire × List Dusk.Pair) := (!v.1.1.1.isEmpty, v)

private theorem dispatch_easy : Easy dispatch :=
  (((Easy.fst.compose Easy.fst).compose Easy.fst).compose (Carry.vacant Unit) |>.compose
    (show Easy (! · : Bool → Bool) from Easy.finite _)).pair Easy.identity

@[simp] private theorem dispatch_wire (A : ℕ) (s : Shape) (r : List Dusk.Pair) :
    dispatch (wire A s,r) = (decide (0 < s.level), wire A s, r) := by
  cases h : s.level with
  | zero => simp [dispatch,wire,h,tally]
  | succ j => simp [dispatch,wire,h,tally_succ]

/-- Bound the encoded descriptor and ordered row, including record markers. -/
theorem payload_size (A : ℕ) (s : Shape) (x : Data s) :
    (buffer A s x).count ≤ 10*(allowance A 1 s+1) := by
  change scale A s + size (flat A s x) + 1 ≤ _
  rw [flat, ← List.map_map, PhysicalWalsh.Padding.marks_size, List.length_map, List.length_range]
  have h : count A s * (4*(s.w+1)+4) ≤ 8*((count A s+1)*(grow A s.level+s.w+1)) := by
    rw [Nat.mul_left_comm 8]
    gcongr <;> omega
  simp only [allowance,pow_one]
  omega

/-- One fixed physical command tags a raw, flat input at any recursion depth. -/
theorem entry {I : Type} (A : ℕ) (s : I → Shape) (x : (t : I) → Data (s t)) :
    BoundedTask (allowance A 1 ∘ s) (allowance A 1 ∘ s)
      (fun t => buffer A (s t) (x t))
      (fun t => .fork (.atom (decide (0 < (s t).level))) (buffer A (s t) (x t))) := by
  have prog := dispatch_easy.on (fun t => (wire A (s t),flat A (s t) (x t)))
  simp only [dispatch_wire] at prog
  apply (BoundedTask.of_time prog).bound 11 21 <;> intro t
  · have := payload_size A (s t) (x t)
    change (buffer A (s t) (x t)).count + 1 ≤ 11*(allowance A 1 (s t)+1)
    omega
  · have := payload_size A (s t) (x t)
    change (buffer A (s t) (x t)).count + (buffer A (s t) (x t)).count + 1 ≤ 21*(allowance A 1 (s t)+1)
    omega

/-- The exact query consumed by the recursively linked interpreter. -/
theorem entry_query {I : Type} {a W : ℕ} (hW : 0 < W) (p : KernelPass.Plan (a+1) W W)
    (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s) (v : I → Invocation hW p) :
    BoundedTask (fun i => allowance (a+1) 1 (v i).shape) (fun i => allowance (a+1) 1 (v i).shape)
      (fun i => buffer (a+1) (v i).shape (v i).row) ((spec hW p scan arena cost).query ∘ v) :=
  entry (a+1) (fun i => (v i).shape) (fun i => (v i).row)

end PhysicalWalshNode.Header

end NearSquareRoot
end Computability
end OAI
