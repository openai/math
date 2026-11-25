import OAI.Computability.BorderVNP.DiagonalPublishedFrontWindows
import OAI.Computability.BorderVNP.DiagonalChargedFrozenOutput
import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask
import OAI.Computability.BorderVNP.PackedLocatedFrozenTable

/-! # A located frozen packet pays its own pre-call route windows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover Packing PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamContraction.ProcessorSlots RoutingISA RoutingISA.Evaluator ScheduleClock _root_.OAI.Computability.BorderVNP.Cube
open TeamScales GeometryAdvice GeometryAdviceRate Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) dlog Q A B j)

/-- The before-and-route estimate on the chosen gate table at one admitted
length, before selecting its rows, declaration, chart or physical memory. -/
def LocatedTableFrontAt (degree fixed emitted H n : ℕ) : Prop :=
  let r := stretch b.ρ n
  let teams := b.physical.teamsPred n
  let w := b.physical.word n
  let start := CoverScale.initialDepth (Epoch.Cube D) r n
  let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start (epochs s.τ n))
  let reserve := SeedPlan.profileReserve r n
  let windows := s.signedWindows degree (512*((cube.pred+1)+Tally.selectorWidth cube.pred cube.copies cube.h+1)) fixed emitted H n r
  ∀ (initial : StartupArena) (desc ceiling l size headerFactor tiles origins : ℕ)
    {install : ℕ → ℕ → Prop} (t : SeedPlan.LocatedFrozenTable reserve w ceiling n r (teams+1) tiles origins install),
    let dir := b.signedStartupDirectory n desc
    let task := b.frozenSignedTask cube n l size headerFactor initial dir reserve ceiling t.outputs w t.directories
    cells≤t.outputs → dir.entries≤t.outputs →
    ∀ pp lp, ∀ axis : ℕ, ∀ after : ℕ → ℕ, let rows := dir.directory pp lp
      let ar := task.cube
      let table := ar.table initial.frame (rows.length+ar.header.d.choose 2)
      let labels := LabelIndex.layout initial.frame after
      ar.stop<2^w → labels.cells=ar.cells → labels.cableCount=ar.cables → labels.deliveryCount=rows.length → labels.labels=ar.alphabet →
      2048*(exterior ((s.τ:ℝ)/5) r n+(teams+1+1)^3+table.count+r+1)≤windows.core ∧
        GeometryAdviceRate.ticks ceiling reserve t.outputs w w+beforeDirectory (teams+1) dir.sites dir.entries+
          rawScheduleTicks ar initial.frame initial.broadcastBase axis teams rows.length after ≤ windows.before

set_option maxRecDepth 7000 in
set_option maxHeartbeats 1400000 in
/-- The actual serialized and interpreted full gate packet bounds both its
arity and interpreter on this schedule, including appended projection banks. -/
theorem JointSchedule.eventually_located_table_front (degree fixed emitted H : ℕ) (phase : E+2≤degree) :
    ∀ᶠ n : ℕ in atTop, LocatedTableFrontAt cube b degree fixed emitted H n := by
  filter_upwards [b.eventually_published_front_windows cube degree fixed emitted H phase,
    b.eventually_word_capacity 1 1,eventually_ge_atTop 1] with n cost bits pos
  unfold LocatedTableFrontAt
  intro r teams w start cells reserve windows initial desc ceiling l size headerFactor tiles origins installer t dir task
    cellsOut entriesOut pp lp axis after rows ar table labels room hc he hr hl
  let P := RoutingISA.Evaluator.publicWork (cube.pred+1) s.α r n (teams+1)
  have wordPos : 1≤w := (GeometryAdviceRate.indexWidths (stretch_one b.ρ n) pos).1.trans bits.1
  have out : t.outputs ≤ packetWords ceiling reserve t.outputs w*w := by
    have h : t.outputs≤t.outputs*w := Nat.le_mul_of_pos_right _ wordPos
    have h' : t.outputs*w ≤ packetWords ceiling reserve t.outputs w := by unfold packetWords; omega
    exact (h.trans h').trans (Nat.le_mul_of_pos_right _ wordPos)
  have cap : ((r*width n (95/100:ℝ):ℕ):ℝ) ≤ P := by
    rw [Nat.cast_mul]
    have col : (width n (95/100:ℝ):ℝ) ≤ (n:ℝ)^(19/20:ℝ) := by
      rw [show (95/100:ℝ)=19/20 by norm_num]
      exact Nat.floor_le (by positivity)
    exact (mul_le_mul_of_nonneg_left col (Nat.cast_nonneg _)).trans (le_add_of_nonneg_right (by positivity))
  have geo : (GeometryAdviceRate.ticks ceiling reserve t.outputs w w:ℝ) ≤ P :=
    (Nat.cast_le.mpr ((Nat.le_add_right _ _).trans t.packet_bound)).trans cap
  have outCap : t.outputs≤⌈P⌉₊ := by
    have h := (Nat.cast_le.mpr (out.trans ((Nat.le_add_left _ _).trans t.packet_bound))).trans cap
    exact_mod_cast h.trans (Nat.le_ceil P)
  let base := Allocation.stop (initial.next+7*dir.candidates) reserve ceiling t.outputs w w
  exact cost desc base reserve ceiling t.outputs w pp lp initial.frame initial.broadcastBase axis after room
    hc he hr hl outCap geo cellsOut entriesOut

end Diagonal

end BorderVNP
end Computability
end OAI
