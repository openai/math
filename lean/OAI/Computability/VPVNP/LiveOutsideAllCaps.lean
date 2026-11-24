import OAI.Computability.VPVNP.LiveOutsidePreparedGroup
import OAI.Computability.VPVNP.LiveOutsideCallCapacity

/-!
# Simultaneous resource bounds for Section 14.2

The site exponent is selected after the public dimensions. For every larger
fixed exponent the length threshold works for every group, route, bounded
advice prefix and native outside trace. The compressed part of a paired
trace has its own Section 13 estimate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideTraces

open BurstRAM OutsideBudget CursorBounds CursorNetwork Filter

theorem eventually_all_caps {C : ℕ} (u : PairExponents C) (c : Constants) (E : UniversalMachine.Program) :
    ∃ B₀, ∀ B ≥ B₀, ∀ᶠ n : ℕ in atTop, ∀ G : PairStages.Group,
      G.g = paperGeometry B (liveCapacity u) n → G.constants = c → G.evaluator = E →
      ∀ raw first last empty, raw ≤ G.constants.prefixCapacity.eval G.g →
        actualBound G.constants G.g raw first last empty < processorCount B n ∧
        max 26 (OutsideTailStages.callBound G.w) ≤ G.g.H ∧
        max 154 (max (5*(2*G.g.d)+23) (OutsideTailStages.instructionBound G)) ≤ n^10000 := by
  obtain ⟨B₀,hs⟩ := eventually_actual c
  refine ⟨B₀,fun B hB => ?_⟩
  filter_upwards [hs B hB,eventually_groupReportCaps u B E] with n size clocks
  intro G hg hc hE raw first last empty hraw
  obtain ⟨per,work⟩ := clocks G hg hE
  refine ⟨?_,per,work⟩
  rw [hg,hc] at hraw ⊢
  exact size (liveCapacity u n) raw first last empty hraw

/-- Application of the common eventual bounds to an actual report list.
All returned inequalities concern the physical words and buckets. -/
theorem eventually_trace_caps {C : ℕ} (u : PairExponents C) (c : Constants) (E : UniversalMachine.Program) :
    ∃ B₀, ∀ B ≥ B₀, ∀ᶠ n : ℕ in atTop, ∀ G : PairStages.Group,
      G.g = paperGeometry B (liveCapacity u) n → G.constants = c → G.evaluator = E →
      ∀ raw first last empty, raw ≤ G.constants.prefixCapacity.eval G.g →
      ∀ (rs : List (Report G.w)) per work,
        Resources rs (actualBound G.constants G.g raw first last empty) per work →
        per ≤ max 26 (OutsideTailStages.callBound G.w) →
        work ≤ max 154 (max (5*(2*G.g.d)+23) (OutsideTailStages.instructionBound G)) →
        RAMBuckets.cost Report.probes rs < processorCount B n ∧
        (∀ r ∈ rs, 1+r.probes ≤ G.g.H ∧ r.events.length+1 ≤ n^10000) := by
  obtain ⟨B₀,h⟩ := eventually_all_caps u c E
  refine ⟨B₀,fun B hB => ?_⟩
  filter_upwards [h B hB] with n fits G hg hc hE raw first last empty hraw rs per work resource hper hwork
  obtain ⟨ct,pc,wc⟩ := fits G hg hc hE raw first last empty hraw
  exact ⟨resource.cost.trans_lt ct,fun r hr => ⟨(resource.calls r hr).trans (hper.trans pc),
    (resource.work r hr).trans (hwork.trans wc)⟩⟩

end LiveProgram.OutsideTraces

end VPVNP
end Computability
end OAI
