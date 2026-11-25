import OAI.Computability.BorderVNP.PackedInheritedWorkHorizon
import OAI.Computability.BorderVNP.PackedFrozenNativeTransport
import OAI.Computability.BorderVNP.PackedFrozenNamedSteps
import OAI.Computability.BorderVNP.PackedFrozenEdgeRectangle
import OAI.Computability.BorderVNP.PackedFrozenPrepHeader
import OAI.Computability.BorderVNP.PackedFrozenSelectedPre
import OAI.Computability.BorderVNP.PackedFrozenSelectedReturn

/-! # Complete physical steps on the original public port coordinates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Inherited WorkWords FrozenTape ProgramSchemas EnrichedOuter SourcePath.NamedRun
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 4500

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (R : Compiled bits deep budget cap w)
    (base : Format) (header : WorkWords.Ports (CoverScale.sites (Cube D) start))
    (leaf : P ↪ Fin (CoverScale.sites (Cube D) start)) (wr : WidthRanges S start T w) (hm : 0 < m)
    (t : ℕ) (ht : t<T)
local notation3 (prettyPrint := false) "beginFmt" => installed S start w t (epoch S start w base t)
local notation3 (prettyPrint := false) "high" => S.high (offset S start t)
local notation3 (prettyPrint := false) "formatAt(" p "," j ")" => inner S.source S.last high S.fanIn (fun i => (before S start t i).edges) p w beginFmt j
local notation3 (prettyPrint := false) "stateAt(" p "," j ")" => (formatAt(p,j)).Output
  (S.source.StatePins S.last high (fun i => (before S start t i).sites) (fun i => (before S start t i).edges) w j)
    (before S start t j).sites w w
local notation3 (prettyPrint := false) "src" => (R.atLevel t ht).program
local notation3 (prettyPrint := false) "native" => NativeTape.steps src beginFmt (header.outer S start t) (privatePorts S leaf t)
  (width_rectangle S deep ht) (tapeEdgeRectangle S deep ht) (wr.successor t ht) hm

/-- All chronological record, width, geometry and guard gates of the selected inner
path, with its original flattened port and histogram coordinates. -/
noncomputable def stageSteps : Steps S.fanIn S.rounds (stagePins S start w base t) (Count S start t (fun _ => w)) :=
  resizeSteps (input_port_count (S:=S) (start:=start) t) (fun p j => stateAt(p,j)) (Count S start t (fun _ => w)) native

/-- The exact named kernel used at a physical stage of the actual augmented machine. -/
theorem stageSteps_size (i : Fin S.rounds) :
    (R.stageSteps base header leaf wr hm t ht i.val i.isLt).size =
      (NativeTape.node src i (stage S start w base t i.val) (header.outer S start t) (privatePorts S leaf t)
        (width_rectangle S deep ht) (tapeEdgeRectangle S deep ht) (wr.successor t ht) hm).size := by
  apply (resizeSteps_size (input_port_count (S:=S) (start:=start) t)
    (fun p j => stateAt(p,j)) (Count S start t (fun _ => w)) native i).trans
  apply (NativeTape.steps_size src beginFmt (header.outer S start t) (privatePorts S leaf t)
    (width_rectangle S deep ht) (tapeEdgeRectangle S deep ht) (wr.successor t ht) hm i).trans
  apply congrArg (fun f : Format => (NativeTape.node src i f (header.outer S start t) (privatePorts S leaf t)
      (width_rectangle S deep ht) (tapeEdgeRectangle S deep ht) (wr.successor t ht) hm).size)
  exact congrArg (fun p => formatAt(p,i.val)) (input_port_count (S:=S) (start:=start) t)

/-- The complete actual outer step, including subdivision, the named history tree
and the final flattened route. Each pass forwards the corresponding immutable records. -/
noncomputable def tapeSteps : Steps (fan S) T (outerPins S start w base) (Machine.Guess S start (fun _ _ => w)) :=
  fun t ht => R.tapeStep base t ht (R.tapePre base t ht (prepHeader t header) (wr.initial t ht))
    (R.stageSteps base header leaf wr hm t ht)

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
