import OAI.Computability.VPVNP.CompressorBlockHeaderRun
import OAI.Computability.VPVNP.CompressorSourceGroups
import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy

/-!
# Branch tapes in the shrinking header and greedy visits

For a successful native call the supplied branch tape equals the choice
bits in its report. The three header visits and six greedy visits all
produce empty tapes, including the indirect operand readers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkHeaderGreedyPackets

open BurstRAM Compression BlockHeaderRun SourceOnline DescriptorSpace BlockPlanner

variable {w : ℕ}

private theorem segment_empty {C : Type*} {P : BurstRAM.Program w C} {fuel count : ℕ} {s : Option (Word w)}
    {m : Memory w} {rs : List (Report w)}
    (run : runSegment P fuel s m (List.replicate count []) = some rs) (r : Report w) (hr : r ∈ rs) :
    choiceBits r.events = [] := by
  have h : choiceBits r.events ∈ branchPaths rs := List.mem_map_of_mem hr
  rw [(runSegment_iff ..).mp run |>.2.2] at h
  exact (List.mem_replicate.mp h).2

/-- All reports of the six native greedy visits have empty branch paths. -/
theorem greedy_reports_empty {a g origin : ℕ} {X : GreedyArena.ShrinkingState a g}
    {T : IncidenceDirectory w} {m : Memory w} (run : GreedyArena.Run X T origin m)
    (r : Report w) (hr : r ∈ run.reports) : choiceBits r.events = [] := by
  simp only [GreedyArena.Run.reports,List.mem_append] at hr
  rcases hr with (((proj|prep)|read)|off)|tag
  · exact (run.projection.work r proj).2.2
  · exact segment_empty run.color.prepRun r prep
  · exact segment_empty run.color.readRun r read
  · exact segment_empty run.offsets.prepRun r off
  · exact segment_empty run.offsets.readRun r tag

private theorem packet_runs {A : Script} {m : Memory w} {ps : List (SourceOnline.Packet A w)}
    (chron : SourceWalk.Chronological Visit.Runs m ps) {p : SourceOnline.Packet A w} (hp : p ∈ ps) :
    p.stage.Runs p.input p.reports := by
  induction ps generalizing m with
  | nil => exact False.elim (List.not_mem_nil hp)
  | cons q qs ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact chron.2.1
    · exact ih chron.2.2 hp

/-- In any chronological packetization of these actual source reports, every
individual call consumes an empty branch tape. -/
theorem empty_choices {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
    {B : S.Templates} {f : B.Entry → R} {hf : B.IsSolution f} (v : SelectedLevel B f hf)
    {L : Layout} {old new : Fin L.levels} {m : Memory w} {six : 6 ≤ L.shape.scalarFields}
    (sub : Substep v L old new six m)
    {a g origin : ℕ} {X : GreedyArena.ShrinkingState a g} {T : IncidenceDirectory w} {start : Memory w}
    (run : GreedyArena.Run X T origin start) {A : Script} {ps : List (SourceOnline.Packet A w)}
    (chron : SourceWalk.Chronological Visit.Runs m ps)
    (logs : ps.flatMap SourceWalk.Packet.reports = reports v L old new m ++ run.reports) :
    ∀ p ∈ ps, ∀ b ∈ p.stage.choices, b = [] := by
  intro p hp b hb
  have actual := packet_runs chron hp
  rw [← ((runSegment_iff ..).mp actual).2.2] at hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
  have mem : r ∈ ps.flatMap SourceWalk.Packet.reports := List.mem_flatMap.mpr ⟨p,hp,hr⟩
  rw [logs] at mem
  rcases List.mem_append.mp mem with head|tail
  · simp only [reports,List.mem_cons,List.not_mem_nil,or_false] at head
    rcases head with rfl|rfl|rfl
    · exact (execute_spec sub.relabel.1).2.2
    · exact (execute_spec sub.advance.1).2.2
    · exact sub.heads.cost.2.2
  · exact greedy_reports_empty run r tail

end CompressorRecords.ShrinkHeaderGreedyPackets

end VPVNP
end Computability
end OAI
