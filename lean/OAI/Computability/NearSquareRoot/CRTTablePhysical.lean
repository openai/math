import OAI.Computability.NearSquareRoot.CRTTableLevel
import OAI.Computability.NearSquareRoot.ShortWordCall

/-! # Physical cost of the level-wide CRT table subroutine -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

/-- One arbitrary complete control setting at one depth. The setting is a
specification parameter. The machine reads the encoded query defined below. -/
structure Setting where
  k : ℕ
  depth : ℕ
  box : List (ℕ × ℕ)
  bits : List Bool
  inverse : Bool
  large : 1 < k
  shape : BoxShape.Valid k (BoxScale.width k) box
  depth_le : depth ≤ k
  bit_count : bits.length ≤ k

def Setting.query (s : Setting) :=
  (s.inverse, tally s.depth, s.box.map (fun p => (tally p.1, tally p.2)), s.bits)

/-- One finite compiled machine and one integer exponent work for every box,
depth, direction, and setting. Its output stack contains the full table
stream. All other register tapes and the return stack are restored, including
their head positions. The clock counts the compiled machine's tape steps. -/
theorem physicalTables :
    ∃ degree : ℕ, ShortWord.PhysicalTask (fun s : Setting => (s.k+1)^degree)
      (fun s => send s.query) (fun s => send (levelTables s.query)) := by
  obtain ⟨cost, ⟨deg, C, estimate⟩, task⟩ :=
    levelTables_budget Setting.k Setting.depth Setting.box Setting.bits Setting.inverse
      Setting.large Setting.shape Setting.depth_le Setting.bit_count
  refine ⟨deg, ShortWord.physicalTask (task.bound (C+1) ?_)⟩
  intro s
  have h := estimate s
  change cost s + 1 ≤ (C+1)*((s.k+1)^deg+1)
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

end CRTTable

end NearSquareRoot
end Computability
end OAI
