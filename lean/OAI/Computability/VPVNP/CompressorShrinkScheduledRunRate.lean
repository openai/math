import OAI.Computability.VPVNP.CompressorShrinkScheduledRun
import OAI.Computability.VPVNP.CompressorShrinkOutputRate
import OAI.Computability.VPVNP.CompressorShrinkGeometryRate
import OAI.Computability.VPVNP.CompressorGroupCost

/-! # The per-position rate of a complete scheduled shrinking pass

The deterministic prefix can be supplied by the default admitted branch.
Its packet count and its actual raw reports agree for every selection, which
suffices for charging it together with the selected row and the chosen
continuation. The coefficient is fixed by the compressor template and
degree transition.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledRun

open BurstRAM Compression ShrinkBlockInputs BlockPlanner DescriptorSpace SourceOnline
open ShrinkOutput ScheduledTrace
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
local notation "prog" => BlockProgram.script B

/-- The scheduled cost bound per incoming position for a complete shrink step, summing the
prefix and geometry, output, and publication tail rates. -/
def fixedRate :=
  groupRate prog (ShrinkScheduledPrefix.prefixRate B i) 36 + ScheduledShrink.outputGroupRate B i + ScheduledShrink.tailGroupRate B

variable (positions blocks round : ℕ) (live : round < blocks) {R : Type*} [CommRing R]
variable (f : B.Entry → R) (hf : B.IsSolution f) {g w : ℕ} (X : GreedyArena.ShrinkingState (a i) g)
variable (base : Word w) (m : Memory w) (fuel cap : ℕ)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "src" => old B i base.val positions blocks round live
local notation "dst" => next B i base.val positions blocks round live

variable {common : ShrinkCurrentBranch.Common B f hf i X base.val positions blocks
  (old B i base.val positions blocks round live) (next B i base.val positions blocks round live) m fuel}
variable {sel : SelectedScore.Selection B X} {tape : List Bool}
variable {pre geom p₅ p₆ p₇ p₈ ms tail : List (Packet (BlockProgram.script B) w)} {marker : Packet (BlockProgram.script B) w}
    {tables : TablesRun w}
local notation "level" => PairSimulation.TraversalRows.shrinkLevel B f hf i X sel tape
local notation "body" => (((p₅++p₆)++p₇)++p₈)

variable {B i positions blocks round live f hf X base m fuel cap}

set_option maxHeartbeats 1500000 in
theorem Result.rate_from
    (h : Result B i positions blocks round live f hf X base m fuel cap common sel tape pre marker geom p₅ p₆ p₇ p₈ ms tail tables)
    (shared : List (Packet prog w)) (count : shared.length=21)
    (reports : shared.flatMap SourceWalk.Packet.reports = BlockHeaderRun.reports level L src dst m ++ common.pre.reports) :
    groupCost prog shared + groupCost prog [marker] + groupCost prog (geom++(body++tail)) ≤ X.positions*fixedRate B i := by
  have firstPart := h.geometry.prefix_rate shared count reports
  have finished := h.finish
  have rest := ScheduledShrink.Output.rate B i X sel base positions blocks round cap finished.output
  have last := ScheduledShrink.tail_rate B i X base positions blocks round cap finished.published
  have bound := Nat.add_le_add (Nat.add_le_add firstPart rest) last
  rw [groupCost_split_selector prog shared marker geom] at bound
  rw [groupCost_append prog geom (body++tail),groupCost_append prog body tail,fixedRate,Nat.mul_add,Nat.mul_add]
  simpa only [Nat.add_assoc] using bound

theorem Result.rate
    (h : Result B i positions blocks round live f hf X base m fuel cap common sel tape pre marker geom p₅ p₆ p₇ p₈ ms tail tables) :
    groupCost prog pre + groupCost prog [marker] + groupCost prog (geom++(body++tail)) ≤ X.positions*fixedRate B i :=
  h.rate_from pre h.geometry.prefixLength h.geometry.prefixReports

/-- The common prefix may come from a different admitted selection and
its own execution. Only its real header and deterministic reports enter
the charge. -/
theorem Result.rate_shared
    (h : Result B i positions blocks round live f hf X base m fuel cap common sel tape pre marker geom p₅ p₆ p₇ p₈ ms tail tables)
    {other : SelectedScore.Selection B X} {word : List Bool} {shared g₀ s₅ s₆ s₇ s₈ m₀ t₀ : List (Packet prog w)}
    {sMarker : Packet prog w} {sTables : TablesRun w}
    (d : Result B i positions blocks round live f hf X base m fuel cap common other word shared sMarker g₀ s₅ s₆ s₇ s₈ m₀ t₀ sTables) :
    groupCost prog shared + groupCost prog [marker] + groupCost prog (geom++(body++tail)) ≤ X.positions*fixedRate B i := by
  apply h.rate_from shared d.geometry.prefixLength
  have same := (ShrinkCurrentBranch.header_eq B f hf i X base.val positions blocks src dst m other word).2.trans
    (ShrinkCurrentBranch.header_eq B f hf i X base.val positions blocks src dst m sel tape).2.symm
  exact d.geometry.prefixReports.trans (congrArg (· ++ common.pre.reports) same)

end CompressorRecords.ShrinkScheduledRun

end

end VPVNP
end Computability
end OAI
