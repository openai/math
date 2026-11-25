import OAI.Computability.BorderVNP.PackedInheritedWorkNamedKernel
import OAI.Computability.BorderVNP.PackedInheritedWorkPrep
import OAI.Computability.BorderVNP.PackedInheritedWorkHorizon
import OAI.Computability.BorderVNP.PackedInheritedWorkCompiledTree

/-! # The actual width-bearing gate families at every selected processor level -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords Packing.PhysicalEpochs EnrichedOuter
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500

variable {D m np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}
variable (C : Compiled bits deep budget cap w) (p : WorkWords.Ports np) (port : P ↪ Fin np)
variable (ranges : WidthRanges S start T w)
/-- The single sequence of gates used by every history. The site rectangles and static
exterior-port columns depend on the schedule, before any histogram is supplied. -/
noncomputable def widthFrames : WidthFrames C where
  pre t ht := (C.atLevel t ht).widthPre rfl (p.outer S start t) (ranges.initial t ht)
  innerStep t ht := (C.atLevel t ht).program.widthSteps (p.outer S start t)
    (width_rectangle S deep ht) (ranges.successor t ht)

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
