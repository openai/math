import OAI.Computability.BorderVNP.DiagonalPublishedArgumentWindow
import OAI.Computability.BorderVNP.DiagonalLocatedTableFront
import OAI.Computability.BorderVNP.DiagonalChosenSignedCalendar

/-! # The argument charge for the two saved banks of the actual frozen table -/

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

open PackedHistoryCircuit.TerminalCells

/-- The selected table pays the real installer's instruction count and all
argument and private-directory work of a native row image. These estimates
precede the choice of declaration, placement, local row data and pin. -/
def LocatedTableArgumentAt (n : ℕ) : Prop :=
  let r := stretch b.ρ n
  let teams := b.physical.teamsPred n
  let w := b.physical.word n
  let reserve := SeedPlan.profileReserve r n
  let ext := exterior ((s.τ:ℝ)/5) r n
  let fixed := (CubeConstants.install (cube.cubeID G)).slots
  let coeff := cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width
    (Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width)
  let budget := (s.chosenSignedWindows cube E n r).argumentsCalls
  ∀ (initial : StartupArena) (desc ceiling l size head tiles origins : ℕ)
    {install : ℕ → ℕ → Prop} (t : SeedPlan.LocatedFrozenTable reserve w ceiling n r (teams+1) tiles origins install),
    let dir := b.signedStartupDirectory n desc
    let task := b.frozenSignedTask cube n l size head initial dir reserve ceiling t.outputs w t.directories
    let ar := task.cube
    ∀ (p d live controls powers : ℕ),
      t.outputs=signedGridOutputCount ar.cables ar.cells dir.entries live controls (CellPacketGeometry.Total p d) →
      powers≤r →
      ∀ pp lp (frame axis : ℕ) (after : ℕ → ℕ),
        let labels := LabelIndex.layout frame after
        let groups := LocalRow.weightLayout ar frame axis
        let allocation := LocalRow.teamLayout ar teams
        ar.stop<2^w → labels.cells=ar.cells → labels.cableCount=ar.cables →
        labels.deliveryCount=(dir.directory pp lp).length → labels.labels=ar.alphabet →
        fixed+argumentDirectory ar.cells dir.entries+
          32*descriptorTicks labels after (ar.alphabet-1) (ar.n+1) groups allocation+
          (82*labels.cableCount+coeff*(ar.alphabet^2+ext+1))+
          cellWork w (2^p+2^d) powers ext ≤ budget

set_option maxRecDepth 6500 in
set_option maxHeartbeats 1400000 in
/-- Increasing the common length threshold suffices for every published
memory at once. The native cell program and the phase meter use the same
fixed cube installer. -/
theorem JointSchedule.eventually_located_table_argument :
    ∀ᶠ n : ℕ in atTop, LocatedTableArgumentAt cube b n := by
  let fixed := (CubeConstants.install (cube.cubeID G)).slots
  let F₀ := cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width
    (Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width)
  let visits := TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width
  filter_upwards [b.eventually_published_argument_window cube (E+2) fixed F₀ visits (le_refl _),
    b.eventually_word_capacity 1 1,eventually_ge_atTop 1] with n paid bits positive
  unfold LocatedTableArgumentAt
  intro r teams w reserve ext scale coeff budget initial desc ceiling l size head tiles origins install t dir task ar
    p d live controls powers shape slots pp lp frame axis after labels groups allocation stop hc he hr hl
  let P := RoutingISA.Evaluator.publicWork (cube.pred+1) s.α r n (teams+1)
  have wordPos : 1≤w := (GeometryAdviceRate.indexWidths (stretch_one b.ρ n) positive).1.trans bits.1
  have cap : ((r*width n (95/100:ℝ):ℕ):ℝ) ≤ P := by
    rw [Nat.cast_mul]
    have col : (width n (95/100:ℝ):ℝ) ≤ (n:ℝ)^(19/20:ℝ) := by
      rw [show (95/100:ℝ)=19/20 by norm_num]
      exact Nat.floor_le (by positivity)
    exact (mul_le_mul_of_nonneg_left col (Nat.cast_nonneg _)).trans (le_add_of_nonneg_right (by positivity))
  have geo : (GeometryAdviceRate.ticks ceiling reserve t.outputs w w:ℝ)≤P :=
    (Nat.cast_le.mpr ((Nat.le_add_right _ _).trans t.packet_bound)).trans cap
  let base := Allocation.stop (initial.next+7*dir.candidates) reserve ceiling t.outputs w w
  exact paid desc base reserve ceiling w p d live controls pp lp frame axis powers after
    stop hc he hr hl wordPos (shape ▸ geo) slots

end Diagonal

end BorderVNP
end Computability
end OAI
