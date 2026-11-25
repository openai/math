import OAI.Hierarchy.DescentRetainedScaledFee

namespace OAI
/-! # A common rate before choosing either public calendar parameter -/
namespace Hierarchy.DescentRetainedSeven
open DescentDatedAddressBook DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section
structure Limits (L : ℕ) where
  chart : Chart
  dimension : chart.retained.high+chart.retained.low≤L
  beforeNodes : chart.retained.previousNodes≤L
  beforeArgs : chart.retained.previousArgs≤L
  afterNodes : chart.retained.nodes≤L
  afterArgs : chart.retained.args≤L
  blocks : chart.retained.blocks≤L
  parts : chart.placement.blocks≤L
  shapes : chart.placement.shapes≤L

theorem fixed_units (r : ℕ) : ∃e:ℕ,∀ᶠ j:ℕ in atTop,∀s:Limits (scale j r),s.chart.units 7≤ scale j e:=by
  apply Chart.scaled_units (J:=id) (fun j (s:Limits (scale j r))=>s.chart) (fun _ _=>7)
  · exact SmallAt.const id 7
  all_goals refine ⟨r,Filter.Eventually.of_forall (fun j s=>?_)⟩
  all_goals first | exact s.dimension | exact s.beforeNodes | exact s.beforeArgs |
    exact s.afterNodes | exact s.afterArgs | exact s.blocks | exact s.parts | exact s.shapes

end
end Hierarchy.DescentRetainedSeven

end OAI
