import OAI.Computability.VPVNP.CompressorShrinkScheduledFinish
import OAI.Computability.VPVNP.CompressorShrinkOutputCharges
import OAI.Computability.VPVNP.CompressorShrinkGeometryCharge

/-! # Scheduled traffic of the shrinking output and DFS publications

The four output windows pay for the resident scans, rectangle intersections,
width rows, ordered-slot construction and the six incidence transfers.
The remaining twenty-one rows have fixed total traffic.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ScheduledShrink

open BurstRAM Compression ShrinkBlockInputs DescriptorSpace SourceOnline BlockPlanner ShrinkOutput
open SlotLevel ShrinkSlots ShrinkSliceSweep ScheduledTrace
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (base : Word w) (positions blocks round cap : ℕ)
local notation "prog" => BlockProgram.script B
local notation "Pkt" => SourceOnline.Packet prog w

/-- The scheduled cost bound per incoming position for shrink output stages 5 through 8,
including scheduler overhead for their visits. -/
def outputGroupRate := groupRate prog (outputRate (a i) (b i)) (ShrinkForward.visitsBefore B i 9)

/-- The scheduled cost bound per incoming position for the shrink publication tail, using a
source charge of 53 and a packet count of 21. -/
def tailGroupRate := groupRate prog 53 21

/-- The retained report lists of a completed output run determine its
entire scheduled charge, with a coefficient fixed before the input. -/
theorem Output.rate {m : Memory w} {ps₅ ps₆ ps₇ ps₈ : List Pkt} {r : TablesRun w}
    (out : Output B i X sel base positions blocks round cap m ps₅ ps₆ ps₇ ps₈ r) :
    let all := ((ps₅++ps₆)++ps₇)++ps₈
    groupCost prog all ≤ X.positions * outputGroupRate B i := by
  intro all
  apply groupCost_le _ _ _ _ _ out.charge
  have n := ShrinkScheduledFinish.output_length B i X sel base positions blocks round cap out
  change 36+all.length = ShrinkForward.visitsBefore B i 9 at n
  exact (show all.length ≤ ShrinkForward.visitsBefore B i 9 by omega).trans
    (Nat.le_mul_of_pos_left _ X.positions_pos)

theorem tail_rate {m : Memory w} {ms ps : List Pkt} (r : ShrinkScheduledTail.Result B base positions blocks round cap i X m ms ps) :
    groupCost prog ps ≤ X.positions*tailGroupRate B := by
  apply groupCost_le
  · rw [r.charge]; exact Nat.le_mul_of_pos_left _ X.positions_pos
  · rw [r.length]; exact Nat.le_mul_of_pos_left _ X.positions_pos

end CompressorRecords.ScheduledShrink

end

end VPVNP
end Computability
end OAI
