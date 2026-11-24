import OAI.Computability.VPVNP.CompressorInitialTraceEquiv
import OAI.Computability.VPVNP.CompressorScheduledTraceData
import OAI.Computability.VPVNP.LiveCompressedPairWorkspaceFrame
import OAI.Computability.VPVNP.LiveCompressedPairReindex

/-! # Physical online descriptor paths from the initial rows and the selected execution

The initial cursor rows and the recursive block trace run on one Fin-11
workspace table. Their framed reports determine the stage path, the memory
handed to the terminal traversal, and the protected headers on every partial
path. The smaller inner clock supplies the room for the outer stage transfer.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace LiveProgram.CompressedPair.DescriptorPaths

open BurstRAM Compression CompressorRecords ScheduledTrace BranchSegments
open PairSimulation.LocalHistory LiveStageLink
open scoped Fin.CommRing

private theorem framed_room {w stages small cap : ℕ} (next : Fin stages → Option (Fin stages))
    (addr : Word w) (stage : Fin stages) (base : Word w) (m : Memory w) (rs : List (Report w))
    (slack : small+3 ≤ cap) (lengths : ∀ r ∈ rs, r.events.length < small) :
    ∀ r ∈ OnlineWorkspace.framed base m rs, room next addr stage (cap+24) r := by
  induction rs generalizing m with
  | nil => simp [OnlineWorkspace.framed]
  | cons r rs ih =>
    rw [OnlineWorkspace.framed,List.forall_mem_cons]
    constructor
    · have length := lengths r List.mem_cons_self
      have framed := (Workspace.report_effect base m r).1
      cases he : (Workspace.report base m r).result <;> cases hn : next stage <;>
        simp only [room,exitReport,he,hn,transferEvents,List.length_append,List.length_cons,List.length_nil,framed] <;> omega
    · exact ih _ (fun q hq => lengths q (List.mem_cons_of_mem _ hq))

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
variable {w cap small total budget a g b n : ℕ} {X : Compression.State a g} {E : StateExecution R b n X}
variable {origin : PassOrigins B f hf E} {W : E.MapWitnesses f} {readers : ExecutionReaders E W}
variable {resident : ScheduledTrace.Resident B f hf w} {past : List (SelectedLevel B f hf)}
variable {pub : Fin 11 → Word w} {pitch : Word w} {m : Memory w}
variable (initial : QuietInterval (BlockProgram.script B) pub cap small (some 0) m)
variable (result : ScheduledTrace.Result resident pub pitch total cap small budget E origin W readers past
    initial.segment.state initial.segment.memory)
local notation "plan" => BlockPlanner.Script.plan (BlockProgram.script B)
local notation "allCut" => initial.withTrace result.trace
private abbrev allowReports (pub : Fin 11 → Word w) (cap : ℕ) (rs : List (Report w)) :=
  ∀ r ∈ rs, room CompressedPair.next (PairTag.address pub) Stage.online (cap+24) r

local notation "allow" => allowReports pub cap

private theorem allowed (slack : small+3 ≤ cap) (z : E.Choices) : allow ((allCut).part z).logs := by
  let core := initial.combinedCore result.trace result.source z
  change allow ((initial.withTrace result.trace).part z).logs
  rw [core.frame]
  exact framed_room _ _ _ _ _ _ slack core.ticks

variable (boot : Bootstrap) (finalTable : PairTable) (clock : ℕ)
variable (hclock : cap+24 = clockAt pub clock Stage.online) (slack : small+3 ≤ cap)

/-- Each mathematical compression choice determines exactly one actual
online stage path on the memory reached after the eight startup calls. -/
def paths : E.Choices ≃ StagePaths boot plan finalTable pub clock Stage.online m :=
  (initial.allAccepted result.trace allow (allowed initial result slack)).trans
    (Equiv.subtypeEquivRight fun bs => by
      change (∃ rs, runSegment (OnlineWorkspace.program plan pub) (cap+24) (some 0) m bs = some rs ∧
        endState (some 0) rs = none ∧ allow rs) ↔
        ∃ rs, runSegment (sourceProgram (components boot plan finalTable) pub Stage.online)
          (clockAt pub clock Stage.online) (some 0) m bs = some rs ∧ endState (some 0) rs = none ∧ _
      rw [source_segment,← hclock]
      rfl)

local notation "e" => paths initial result boot finalTable clock hclock slack

theorem paths_bits (z : E.Choices) : (e z).val = ((allCut).part z).bits :=
  initial.allAccepted_bits result.trace allow (allowed initial result slack) z

theorem paths_reports (z : E.Choices) : ordinaryReports (e z) = ((allCut).part z).logs := by
  have run := ordinaryRun (e z)
  rw [source_segment,paths_bits] at run
  conv_lhs at run => arg 2; rw [← hclock]
  exact Option.some.inj (run.symm.trans ((allCut).part z).run)

/-- The final RAM handed to the next stage contains the selected execution's
entire post-memory and the terminal-stage tag written by the transfer. -/
theorem paths_post (z : E.Choices) :
    onlinePost (e z) = writeMemory (result.trace.cut.part z).memory (PairTag.address pub) (tagWord w Stage.terminal) := by
  rw [onlinePost,paths_reports]
  change writeMemory ((allCut).part z).memory _ _ = _
  rw [initial.withTrace_memory]
  rfl

/-- The combined log includes the initial cursor rows and each chosen block
exactly once. Every inner call contributes six extra framing probes. -/
theorem paths_cost (z : E.Choices) :
    let core := initial.combinedCore result.trace result.source z
    RAMBuckets.cost Report.probes (ordinaryReports (e z)) ≤
      6*core.logs.length + RAMBuckets.cost Report.probes initial.source.logs + budget := by
  intro core
  rw [paths_reports]
  rw [core.frame,(OnlineWorkspace.framed_effect (pub 2) m core.logs (some 0)).2.2]
  have hc := initial.combinedCost result.trace result.source z
  change RAMBuckets.cost Report.probes core.logs = _ at hc
  rw [hc,Nat.add_assoc]
  exact Nat.add_le_add_left (Nat.add_le_add_left (result.cost z) _) _

/-- The unframed reports and their cost are those of the very same chronological
choice, including the initial interval and each subsequent pass. -/
theorem paths_core (z : E.Choices) :
    let core := initial.combinedCore result.trace result.source z
    ordinaryReports (e z) = OnlineWorkspace.framed (pub 2) m core.logs ∧
      RAMBuckets.cost Report.probes core.logs ≤ RAMBuckets.cost Report.probes initial.source.logs+budget := by
  intro core
  refine ⟨(paths_reports initial result boot finalTable clock hclock slack z).trans core.frame,?_⟩
  have cost := initial.combinedCost result.trace result.source z
  change RAMBuckets.cost Report.probes core.logs = _ at cost
  rw [cost]
  exact Nat.add_le_add_left (result.cost z) _

include result hclock in
private theorem keep {st : Word w} {mem : Memory w} {bits : List Bool} {r : Report w}
    (reach : SourceReachable boot plan finalTable pub clock Stage.online m st mem)
    (call : execute (original boot plan finalTable pub Stage.online) (clockAt pub clock Stage.online)
      ((original boot plan finalTable pub Stage.online).start st) mem bits = some r)
    (x : ℕ) (hx : x < (pub 2).val+6) : after mem r.events x = mem x := by
  apply reach.online_keep_of_prefix (lo := (pub 2).val+6) _ call x hx
  intro bs rs run
  rw [← hclock] at run
  exact initial.withTrace_stable result.trace result.frame run

/-- The low bank frame holds even on a successful native prefix whose
unprocessed motifs have no accepting extension. -/
def protectedStage (below : (PairTag.address pub).val < (pub 2).val+6) :
    Protected boot plan finalTable pub clock Stage.online m :=
  Protected.ofSource boot plan finalTable pub clock Stage.online m
    (fun reach _ call _ => keep initial result boot finalTable clock hclock reach call _ below)

theorem protectedStage_word (below : (PairTag.address pub).val < (pub 2).val+6)
    (x : ℕ) (hx : x < (pub 2).val+6) :
    (protectedStage initial result boot finalTable clock hclock below).word x :=
  Protected.ofSource_word boot plan finalTable pub clock Stage.online m x
    (fun reach _ call _ => keep initial result boot finalTable clock hclock reach call _ below)
    (fun reach _ call => keep initial result boot finalTable clock hclock reach call x hx)

end LiveProgram.CompressedPair.DescriptorPaths

end

end VPVNP
end Computability
end OAI
