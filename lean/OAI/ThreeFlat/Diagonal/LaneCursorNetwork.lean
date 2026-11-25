import OAI.ThreeFlat.Diagonal.LaneCursorTrace
import OAI.ThreeFlat.Diagonal.LaneCursorPorts

namespace OAI
/-! # The initial physical cursor network for the trace -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout

open scoped BigOperators Classical

variable {F : Type*} [CommSemiring F] {p k low offsets slots r : ℕ}
variable {N : BitNetwork F p} (P : RowLayout N (k + 1) low offsets slots)

/-- The original trace valuation is the contraction of genuine local,
two-sided tensors on the lifted cursor graph. Each incoming string is
the label of the unique outgoing slot matched to it by `actualTarget`. -/
theorem eval_cursor_graph (hk : 2 ≤ k + 1) (pin : Fin p → Bool) :
    (∑ edges : Fields (k + 1) r (Fin offsets) (PayloadAddress low slots),
      ∏ i, ∏ lane, portTensor P.mask (P.localTensor pin) i lane
        (outgoingPorts edges i lane) (incomingPorts hk edges i lane)) = N.eval pin := by
  simp_rw [portTensor_eq]
  exact P.eval_cursor pin

/-- The bit width of each physical arc is the bucket size times the
number of offset, per-row cell and argument choices. -/
theorem width (offsets low slots : ℕ) :
    Fintype.card (Fin offsets × PayloadAddress low slots) =
      2 ^ low * (offsets * slots * 3) := arc_width ..

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
