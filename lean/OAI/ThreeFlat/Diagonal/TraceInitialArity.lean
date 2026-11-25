import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule
import OAI.ThreeFlat.Diagonal.LaneCursorEnergy

namespace OAI
/-! # Fitting an initially thickened binary cursor to the first physical shrink -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open LaneCursor
open scoped BigOperators
variable {F : Type} [Field F] (B : Block F)

/-- Additional copies per port direction, beyond the first physical slot. -/
def cursorCopies := 2^(B.exponent 0-1)-1

theorem cursor_degree : (B.cursorCopies+1)*2=2^(B.exponent 0) := by
  have h : 2≤2^(B.exponent 0) := by have := B.restore; have := B.hh; omega
  have he : 0<B.exponent 0 := by
    by_contra! hz
    have z : B.exponent 0=0 := by omega
    simp [z] at h
  have sz : 0<(2:ℕ)^(B.exponent 0-1) := by positivity
  unfold cursorCopies
  rw [Nat.sub_add_cancel (by omega : 1≤2^(B.exponent 0-1)),←pow_succ]
  congr 1
  omega

/-- The seed bound applies directly to the constant-width physical stream
at the first degree used by every nonempty block program. -/
theorem cursor_energy (k low offsets slots : ℕ) :
    Real.sqrt (∑ _ : Arc k (2^(B.exponent 0)),
      ((2^low*(offsets*slots*3) : ℕ):ℝ)^2 /
        (1/(((k*2^k : ℕ):ℝ)*(2^(B.exponent 0):ℕ)))) ≤
      ((k*2^k : ℕ):ℝ)*(2^(B.exponent 0):ℕ)*(2^low*(offsets*slots*3) : ℕ) := by
  apply sqrt_initial_energy
  intro _
  exact (arc_width offsets (2^low) slots 3).symm.le

end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
