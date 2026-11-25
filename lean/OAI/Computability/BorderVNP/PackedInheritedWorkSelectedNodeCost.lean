import OAI.Computability.BorderVNP.PackedInheritedWorkNodeRectangle
import OAI.Computability.BorderVNP.PackedInheritedWorkSelectedPreCost
import OAI.Computability.BorderVNP.PackedInheritedWorkNamedCost
import OAI.Computability.BorderVNP.PackedInheritedWorkHorizon

/-! # Sparse width-gate charge at the real selected node -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity Packing Packing.Inherited
open Packing.Inherited.WorkWords EnrichedOuter TeamScales
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1200000

variable {D m np : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- Coefficient of the scan and birth-word operations for each row of the joined children. -/
noncomputable def widthNodeFactor : ℕ := (4100+100*(2*e.count+1+birthNodes e))*widthScanFactor S*65^3

variable {S} {P : Type} [Fintype P] {bits : P → ℕ} {n r start T : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (C : Compiled bits deep budget cap (60*logWidth r n))

/-- The additional width gates of the actual selected inner step cost one cubic word
polynomial per row of its input rectangle, including every exterior port and birth guess. -/
theorem Compiled.widthSteps_rowWork (p : WorkWords.Ports np) (base : np ≤ CoverScale.sites (Cube D) start)
    {t : ℕ} (ht : t<T) (wr : WidthRanges S start T (60*logWidth r n)) (i : Fin S.rounds) {den cut : ℕ}
    (range : Ranges S r n start t i den cut) (hL : 1 ≤ logWidth r n)
    (hseeds : seedCount S start t i ≤ CoverScale.sites (Cube D) start*bins S) :
    let A := C.atLevel t ht
    let step := A.program.widthSteps (p.outer S start t) (width_rectangle S deep ht) (wr.successor t ht)
    (step i.val i.isLt).size ≤ (C.nodes t ht i).size + rowWork (widthNodeFactor S) (CoverScale.sites (Cube D) start)
      (logWidth r n) 3 ((before S start t i).parallel S.fanIn) := by
  intro A step
  let N := S.fanIn*Parallel.nestedCapacity S.fanIn (portCapacity S np t) i.val
  let L := logWidth r n
  let R := widthScanRows S start t i N
  let V := CoverScale.sites (Cube D) start
  let next := before S start t (i.val+1)
  let sub := (before S start t i).parallel S.fanIn
  have ports : N ≤ sub.sites := Nat.mul_le_mul_left S.fanIn (widthPorts_le S base t i.val)
  have rows : 1+CellAddressCircuit.count next.sites next.edges N next.sites ≤ R := Nat.le_add_right _ _
  have seeds : S.source.stageSeeds S.last (S.high (offset S start t)) i ≤ R := by
    rw [stageSeeds_offset S deep ht i]
    exact Nat.le_add_left _ _
  have raw := A.program.widthSteps_cubic (p.outer S start t) (width_rectangle S deep ht) (wr.successor t ht) i
    rows seeds (show 60*L ≤ 64*L by omega) (widthScanRows_log S range hL ports)
  exact raw.trans (Nat.add_le_add_left (widthScanRows_cubic S _ hL hseeds ports) _)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
