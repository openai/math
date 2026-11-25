import OAI.Optimization.LinearProgramming.RAM.Basic
import Lean.Elab.Tactic.Omega

/-! Elementary sizes of the ordinary rational input tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

/-- Any coefficient on the input tape contributes to its total binary length. -/
theorem member_bits_le_totalBits {q : ℚ} {tape : List ℚ} (hq : q ∈ tape) :
    ratBits q ≤ totalBits tape := by
  induction tape with
  | nil => simp at hq
  | cons a t ih =>
    rcases List.mem_cons.mp hq with rfl | h
    · simp [totalBits]
    · exact (ih h).trans (Nat.le_add_left _ _)

/-- The scalar tape has at least one bit per entry, including zero entries. -/
theorem entry_count_le_totalBits (tape : List ℚ) : tape.length ≤ totalBits tape := by
  induction tape with
  | nil => simp [totalBits]
  | cons a t ih =>
    have h : 1 ≤ ratBits a := by unfold ratBits; omega
    change t.length + 1 ≤ ratBits a + totalBits t
    omega

end RAM
end LinearProgramming
end Optimization
end OAI
