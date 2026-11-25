import OAI.Computability.NearSquareRoot.CRTPositionClock

/-! # Charging the physical sweep against a larger width

The emitted stream depends on the position table and address width alone.
Increasing the width in the clock bound can therefore pay for both polynomial
overheads while the machine operates on the original array of records.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

theorem tableMass_le_ghostWidth (ρ : ℝ) (s : TableShape) (d D : ℕ) :
    tableMass ρ s d ≤ tableMass ρ { s with width := s.width + (s.k+1)^D } d := by
  unfold tableMass
  dsimp only
  have width : (s.width : ℝ) ≤ (s.width + (s.k+1)^D : ℕ) := by
    exact_mod_cast Nat.le_add_right _ _
  gcongr

/-- Padding the bound alone pays for the preparation clock and the per-row
polynomial degree. The clock on the left uses the physical record width. -/
theorem table_raw_clock_le {ρ : ℝ} (hρ : 0 ≤ ρ) (s : TableShape) (a d D B C : ℕ)
    (ha : a ≤ D) (hd : d ≤ D) :
    ((B * (s.k+1)^a + s.stream.length * ((C+2)*⌈tableMass ρ s d⌉₊) + 2 : ℕ) : ℝ) ≤
      ((B + 5412*(C+2) + 2 : ℕ) : ℝ) * tableRate ρ s.k (s.width+(s.k+1)^D) := by
  let t := { s with width := s.width + (s.k+1)^D }
  have fit {j : ℕ} (h : j ≤ D) : (t.k+1)^j ≤ t.width :=
    (Nat.pow_le_pow_right (Nat.succ_pos s.k) h).trans (Nat.le_add_left _ _)
  have ceil : ⌈tableMass ρ s d⌉₊ ≤ ⌈tableMass ρ t d⌉₊ :=
    Nat.ceil_mono (tableMass_le_ghostWidth ρ s d D)
  refine le_trans ?_ (table_clock_le hρ t a d B C (fit ha) (fit hd))
  exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left s.stream.length
    (Nat.mul_le_mul_left (C+2) ceil)) (B*(s.k+1)^a)) 2

/-- The enlarged clock is the native row count times the enlarged width and the
position-permutation factor. -/
theorem tableRate_ghostWidth (ρ : ℝ) (s : TableShape) (D : ℕ) :
    tableRate ρ s.k (s.width+(s.k+1)^D) = ((2^s.k : ℕ) : ℝ) *
        ((s.width+(s.k+1)^D : ℕ) : ℝ) * positionRate ρ s.k :=
  tableRate_eq ..

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
