import OAI.Hierarchy.ProbeOuterAccount

namespace OAI
/-! # The signed potential after an integer stock cap -/

namespace Hierarchy.AdaptiveProbe.OuterBank

open scoped BigOperators Classical
noncomputable section

variable {I X : Type*} [Fintype I] (B : OuterBank I X)

/-- An actual width-limited router retains the clipped stock and bills the
observed excess at most its box price. The resulting balance is bounded by the
cash before spilling plus the potential of the full requested stock. -/
theorem capped_balance (x : X) (raw : I → ℕ) (paid : ℝ) {w cap : ℕ} {s : ℝ}
    (hw : 0<w) (ha : 0<B.a) (hb : ∀ i, 0≤B.coefficient i) (hM : 0≤B.M) (hs : 0<s)
    (saturates : ∀ i, s*rowSlope B.a (B.coefficient i) B.M (B.box i) ≤ cap)
    (stored : ∀ i, B.stock x i = min (raw i) (cap*w))
    (routed : B.cash x ≤ paid + pairing (bitStock w (spillBits cap w raw)) B.box) :
    B.balance w s x ≤ paid + potential B.a B.M s B.coefficient B.box (bitStock w raw) := by
  have keep : B.stock x = clipBits cap w raw := funext stored
  change B.cash x + potential B.a B.M s B.coefficient B.box (bitStock w (B.stock x)) ≤ _
  rw [keep, outer_stock_cap cap B.coefficient B.box raw hw ha hb hM hs saturates]
  exact add_le_add routed le_rfl

end
end Hierarchy.AdaptiveProbe.OuterBank

end OAI
