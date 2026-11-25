import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryTraces
import OAI.Optimization.LinearProgramming.PriceGame.TrialMarketFractionSize
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionStep

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States.Mass Moment TrialExecution

/-- The signed gain actually recorded at this step is computed from the deterministic
clearing market and its real feedback labels. The final group writes an exact zero. -/
theorem executeStep_emits_gain_bits {N ne r l j L d B : ℕ} (es : Fin ne → Expert N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N) (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (hl : 0<L) (hd : L≤2^d) (xs : Fin j → Call N ne r l)
    (hlocal : ∀ e, (incomingLocal es w xs e).den ∣ L ∧ RAM.ratBits (incomingLocal es w xs e) ≤ B)
    {tr rc} (h : Emits (executeStep es (marketSolverAtCommonWeightUnit es) w hw history path child j xs) tr rc)
    (e : Fin ne) : RAM.ratBits (rc.val.data.gain[e]) ≤ 3+2*(B+d) := by
  rw [rc.property.gain_eq e]
  by_cases hj : j<r
  · simp only [executeStep, dite_eq_left hj] at h
    obtain ⟨_, _, _, _, _, rest⟩ := h.bind_inv
    obtain ⟨labels, _, rfl⟩ := rest.map_inv
    have z := (market_fraction_gain_of_registers es history (incomingLocal es w xs)
      (incomingLocal_nonneg es w hw xs) L d B hl hd hlocal e labels).2 Finset.univ
    exact z
  · simp only [executeStep, dite_eq_right hj] at h
    obtain ⟨_, _, rfl⟩ := h.map_inv
    change RAM.ratBits (gainQ (fun (_ : Fin ne) (_ : Vertex N l) => 0) _ _ e) ≤ _
    simp only [gainQ, zero_mul, Finset.sum_const_zero]
    exact Nat.le_add_right 3 _

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
