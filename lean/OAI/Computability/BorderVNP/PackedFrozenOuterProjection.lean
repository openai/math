import OAI.Computability.BorderVNP.PackedHistoryWrappedProjection
import OAI.Computability.BorderVNP.PackedFrozenBoundaryProjection

/-! # Projecting the real subdivision and return around all inner histogram words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Inherited WorkWords FrozenTape ProgramSchemas EnrichedOuter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1500000
set_option maxRecDepth 4500

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (R : Compiled bits deep budget cap w)
    (base : Format) (t : ℕ) (ht : t<T) (header : WorkWords.Ports (portSlots S start t 0))
    (fits : (before S start t 0).sites ≤ 2^w)
local notation3 "geo" j => Boundary.Pins S start (boundaryShape S start) w j
local notation3 "full" j => outerPins S start w base j

/-- The actual prepared and returned tape frame projects on all words whenever
the inner combining nodes project on all words. The original outer child geometry
and every selected root pin are passed to the same public placement procedure. -/
theorem tapeStep_project
    (nodes : Steps S.fanIn S.rounds (stagePins S start w base t) (Count S start t (fun _ => w)))
    (correct : StepsProject (fun _ z => .inl (.inl z)) nodes (R.machine t ht).step)
    (xg : LocalPins (fan S) (full t) (Machine.Guess S start (fun _ _ => w) t) → Bool) (r : Result (geo (t+1))) :
    (R.tapeStep base t ht (R.tapePre base t ht header fits) nodes).eval xg (Sum.map (fun z => .inl (.inl z)) id r) =
      (R.machine.steps t ht).eval (xg ∘ Sum.map (Prod.map id (fun z => .inl (.inl z))) id) r := by
  let before (z : Fin (fan S) × (geo t)) : Fin (fan S) × (full t) := (z.1,.inl (.inl z.2))
  let after (z : geo (t+1)) : full (t+1) := .inl (.inl z)
  exact correct.wrappedEpoch before after (R.tapePre base t ht header fits) (R.machine t ht).pre
    (R.tapePost base t ht) (R.machine t ht).post (R.tapePre_geometry base t ht header fits)
    (R.tapePost_geometry base t ht) xg r

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
