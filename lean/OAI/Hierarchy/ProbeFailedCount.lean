import OAI.Hierarchy.ProbeFailure
import OAI.Hierarchy.ProbeBoxBound

namespace OAI
/-! # Count genuinely failed rows after the controller's two discrepancy roundings -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

/-- Actual integer discrepancy words define both the per-row fail mask and the global
sum. Every selected row has a provably failing *actual* price vector and the true scan
has positive density, also when masks come from several differently named formats. -/
theorem selected_failed_count {n d Q : ℕ} (r : Fin n → ℕ) (actual : Fin n → ℝ) (adj : Fin n → Fin d → Fin n)
    (symm : ∀ v i, ∃ j, adj (adj v i) j=v) {ε C : ℝ} (_he : 0<ε) (hC : 0≤C) (hQ : 0<Q)
    (bound : ∀ v, (r v:ℝ)/Q ≤ C) (accuracy : ∀ v, |(r v:ℝ)/Q-actual v|≤ε)
    (large : 4*ε*n*Q≤∑v,(r v:ℝ)) :
    let fail := fun v => decide (2*ε<(r v:ℝ)/Q)
    2*ε*n≤(ProtocolConflictPack.picked fail adj).card*(d+1:ℝ)*C ∧
    ∀v∈ProtocolConflictPack.picked fail adj, ε < actual v := by
  intro fail
  have pos : 0<(Q:ℝ) := by exact_mod_cast hQ
  have big : 2*ε*n+2*ε*n≤∑v,(r v:ℝ)/Q := by
    rw [←Finset.sum_div,le_div_iff₀ pos]; convert large using 1; ring
  refine ⟨failed_packing (fun v => (r v:ℝ)/Q) adj symm hC bound big,?_⟩
  intro v hv
  have yes := ((ProtocolConflictPack.chosen_iff fail adj v).mp (Finset.mem_filter.mp hv).2).1
  have high : 2*ε<(r v:ℝ)/Q := of_decide_eq_true yes
  linarith [(abs_le.mp (accuracy v)).2]

end
end Hierarchy.AdaptiveProbe

end OAI
