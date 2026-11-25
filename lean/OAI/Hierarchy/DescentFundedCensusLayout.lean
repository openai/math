import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Storage for the reset's pre-compaction charged record counts -/
namespace Hierarchy.DescentFundedCensus
open DescentSIMDLookup

structure Shape where
  jobs : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  bits : ℕ
  broadcast : ℕ

namespace Shape
variable (s : Shape)

def rows := s.hosts * chunks s.groups s.lanes
def width := s.broadcast * s.lanes
def pageCount := 2 * (s.jobs + 1)
def out (base : ℕ) := base + s.pageCount * 2^s.width
def used (base : ℕ) := s.out base + s.jobs * s.rows
def roof (base : ℕ) := s.out base + 2^(Nat.clog 2 (s.jobs*s.rows))
def column (base : ℕ) (j : Fin s.jobs) := s.out base + j.val * s.rows

theorem shift (base : ℕ) : s.roof base = base + s.roof 0 := by simp [roof,out,Nat.add_assoc]
theorem room (base : ℕ) : base ≤ s.roof base := by rw [s.shift]; exact Nat.le_add_right ..
theorem padded (base : ℕ) : s.used base ≤ s.roof base := Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
theorem output_room (base : ℕ) : s.out base ≤ s.roof base := Nat.le_add_right ..

end Shape
end Hierarchy.DescentFundedCensus

end OAI
