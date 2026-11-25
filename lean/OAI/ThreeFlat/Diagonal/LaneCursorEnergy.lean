import OAI.ThreeFlat.Diagonal.LaneCursorRelay
import OAI.Computability.VPVNP.CompressionBudget

namespace OAI
/-! # Position count and initial wire energy of the trace cursor -/

namespace ThreeFlat.Diagonal.LaneCursor
open scoped BigOperators

abbrev Arc (k degree : ℕ) := (Fin k × Fin degree) × Lane k

theorem positions_card (k : ℕ) : Fintype.card (Fin k × Lane k) = k * 2 ^ k := by
  simp only [Lane, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

theorem arcs_card (k degree : ℕ) : Fintype.card (Arc k degree) = (k * 2 ^ k) * degree := by
  simp only [Arc, Lane, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ac_rfl

/-- Every actual arc reserves one bit per offset, low row, local cell
ordinal and argument. Applying the regular equal-mass energy bound gives
the product of actual positions, degree, and this explicit width. -/
theorem sqrt_initial_energy (k degree low offsets slots : ℕ)
    (w : Arc k degree → ℕ)
    (fits : ∀ e, w e ≤ Fintype.card (Fin offsets × (Fin (2 ^ low) × Fin slots × Fin 3))) :
    Real.sqrt (∑ e, (w e : ℝ) ^ 2 / (1 / (((k * 2 ^ k : ℕ) : ℝ) * degree))) ≤
      ((k * 2 ^ k : ℕ) : ℝ) * degree * (2 ^ low * (offsets * slots * 3) : ℕ) := by
  exact Computability.VPVNP.Compression.regularWire_sqrtEnergy_le w (arcs_card _ _) fun e =>
    (fits e).trans_eq (arc_width offsets (2 ^ low) slots 3)

end ThreeFlat.Diagonal.LaneCursor

end OAI
