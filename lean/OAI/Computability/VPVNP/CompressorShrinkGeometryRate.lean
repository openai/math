import OAI.Computability.VPVNP.CompressorShrinkScheduledGeometry
import OAI.Computability.VPVNP.CompressorShrinkPrefixCharge

/-! # Charging the selected group after a common shrinking prefix -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledGeometry

open BurstRAM BlockPlanner DescriptorSpace Compression BlockHeaderRun SourceOnline
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → R} {hf : B.IsSolution f} {i : Fin S.steps}
variable {g w : ℕ} {X : GreedyArena.ShrinkingState (ShrinkBlockInputs.a i) g}
variable {sel : SelectedScore.Selection B X} {tape : List Bool} {base : Word w} {positions blocks t : ℕ}
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "level" => PairSimulation.TraversalRows.shrinkLevel B f hf i X sel tape
local notation "Pkt" => SourceOnline.Packet prog w
variable {old new : Fin (BlockProgram.layout B base.val positions blocks).levels} {m : Memory w}
local notation "start" => tableBase L old (0 : Fin 6)
local notation "T" => packedIncidence L w old (DemandRAM.oldCount X)
local notation "initial" => finalMemory level L old new m
local notation "headers" => BlockHeaderRun.reports level L old new m

set_option maxHeartbeats 1000000 in
/-- A prefix with the same native reports and number of calendar rows as
this branch incurs the same traffic when the chosen geometry follows it. -/
theorem Result.prefix_rate {fuel : ℕ} {p : ShrinkBranch.Prefix X T start fuel initial}
    {v : ShrinkBranch.Selected B X T start (10 : Word w) (B.shrink.selectorBits : Word w) fuel initial p sel}
    {pre : List Pkt} {selector : Pkt} {tail : List Pkt} {cap : ℕ}
    (h : Result B f hf i X sel tape base positions blocks t old new m fuel p v cap pre selector tail)
    (shared : List Pkt) (count : shared.length=21)
    (logs : shared.flatMap SourceWalk.Packet.reports = headers++p.reports) :
    ScheduledTrace.groupCost prog (shared++selector::tail) ≤
      X.positions*ScheduledTrace.groupRate prog (ShrinkScheduledPrefix.prefixRate B i) 36 :=
  (ShrinkScheduledPrefix.group_charge B f hf i X sel tape base positions blocks old new m T start
    (10 : Word w) (B.shrink.selectorBits : Word w) (p:=p) v (pre:=shared) (last:=selector) (geo:=tail)
    (mem:=selector.output) logs h.selectReports count h.suffixLength h.suffix.chronological h.suffixEvents h.suffixTapes).2.2

end CompressorRecords.ShrinkScheduledGeometry

end

end VPVNP
end Computability
end OAI
