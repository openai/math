import OAI.Computability.VPVNP.CompressorBlockIndex
import OAI.Computability.VPVNP.CompressorScriptWindow
import OAI.Computability.VPVNP.CompressorSourceSequence
import OAI.Computability.VPVNP.CompressorShrinkTermPacketBounds
import OAI.Computability.VPVNP.CompressorShrinkTermVisitReadback

/-!
# The two shrinking term packets in the repeated online block

The gather occupies ordinal 20 of its shrinking substep, and the fused
term selector occupies ordinal 21. The stage occurrences retain the
original resetting instruction programs, physical operands, bit streams
and reports when placed into the global script.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkTermOnline

open BurstRAM BlockPlanner Compression Schedule DescriptorSpace ShrinkBlockInputs ShrinkTermPackets
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
local notation "A" => BlockProgram.script B
local notation "F" => BlockProgram.geometry B
local notation "O" => BlockProgram.arena B i.val 0

/-- The header, greedy and bundle visits that precede term gathering within this shrinking
substep. -/
def prior := BlockHeaderPlan.substep F i.val (.shrink (a i) (b i)) ++
  GreedyLevelPlan.visits F i.val (a i) O ++ ShrinkBundlePlan.visits F i.val (a i) O

/-- The selected placement and later slice and slot visits following term selection in this
shrinking substep. -/
def remaining :=
  let prepared := ShrinkBlockInputs.beforeSlices B F i O
  SelectedPlan.visits (selectedInputs B F i O) (a i) ++ (BlockProgram.shrink B i).drop prepared.length

theorem prior_length : (prior B i).length = 20 := by
  simp only [prior,List.length_append,BlockHeaderPlan.substep_length,GreedyLevelPlan.visits_length,ShrinkBundlePlan.visits_length]

/-- The exact two-visit interval occupied by demand gathering and term selection in the
repeated block script. -/
def window : BlockPlanner.Window A (termVisits B i O) where
  before := BlockIndex.earlier B i ++ prior B i
  after := remaining B i ++ BlockIndex.later B i
  block := by
    change BlockProgram.block B = _
    rw [BlockIndex.split_block B i]
    simp only [prior,remaining,BlockProgram.shrink,List.append_assoc,List.drop_left]
    simp only [ShrinkBlockInputs.beforeSlices,List.append_assoc]

/-- Number the gather as the first term visit and the selector as the second. -/
def localIndex : Stage → Fin (termVisits B i O).length
  | .gather => ⟨0,by rw [termVisits_length]; decide⟩
  | .select => ⟨1,by rw [termVisits_length]; decide⟩

/-- Map the gather or selector through its two-visit window to its global script index. -/
def index (j : Stage) : Fin (A).size := (window B i).index (localIndex B i j)

theorem index_visit (j : Stage) : (A).visit (index B i j) = ShrinkTermPackets.visit B i O j := by
  cases j <;> exact (window B i).visit (localIndex B i _)

/-- The chronological phase ordinal of a term visit at a given block repetition, after the
initial sequence and earlier substeps. -/
def ordinal (iteration : ℕ) (j : Stage) :=
  (A).initial.length+iteration*(A).block.length+(BlockIndex.earlier B i).length+20+(localIndex B i j).val

theorem calendar (iteration : ℕ) (j : Stage) :
    (Online.calendar (A).plan).phase (ordinal B i iteration j) = (index B i j).val ∧
      (Online.calendar (A).plan).level (ordinal B i iteration j) = iteration := by
  let n := (window B i).position (localIndex B i j)
  have offset : n.val = (BlockIndex.earlier B i).length+20+(localIndex B i j).val := by
    change ((BlockIndex.earlier B i ++ prior B i).length+(localIndex B i j).val) = _
    rw [List.length_append,prior_length]
  have h := (A).block_phase iteration n
  have e : ordinal B i iteration j = (A).initial.length+iteration*(A).block.length+n.val := by rw [offset,ordinal]; omega
  rw [e]; exact h

variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (s : X.ShrinkSelection B.shrink) (fuel : ℕ)

/-- Install the chosen term worker at its global index with the physical operand bank,
motif-count stop and gather or selection tapes. -/
def globalVisit (j : Stage) : SourceOnline.Visit A w :=
  SourceOnline.Visit.ofWorker (index B i j) (ShrinkTermPackets.visit B i O j).worker
    (congrArg BlockPlanner.Visit.worker (index_visit B i j))
    fuel 0 (ShrinkTermInputs.motifCount X : Word w) (bank B i O X T start j) (choices (w := w) B i X s j)

theorem runs (j : Stage) (mem : Memory w) (rs : List (Report w))
    (packet : PacketRun B i O X T start s fuel j mem rs) :
    (globalVisit B i X T start s fuel j).Runs mem rs := (SourceOnline.Visit.ofWorker_runs ..).mpr packet.run

theorem checked (L : DescriptorSpace.Layout) (cap : ℕ) (j : Stage) (mem : Memory w) (rs : List (Report w))
    (packet : PacketRun B i O X T start s fuel j mem rs)
    (hpos : 0 < fuel) (room : ShrinkInput.termEnd X start 10 < 2^w) (dataStart : levelStart L 0 ≤ start)
    (recipeClock : ((A).plan.recipes (index B i j)).2.code.length+1+2*Online.N (A).size (A).size+5 ≤ cap)
    (dataClock : fuel+3+4*(((A).catalog (index B i j)).params+1)+2*Online.N (A).size (A).size+5 ≤ cap) :
    SourceOnline.Checked A L cap ⟨globalVisit B i X T start s fuel j,mem,rs⟩ := by
  have hn := ShrinkTermSelection.motifCount_eq X
  have fits : ShrinkTermInputs.motifCount X < 2^w := by
    rw [hn]; unfold ShrinkInput.termEnd at room; omega
  obtain ⟨rd,wr⟩ := packet.arena room
  exact ⟨hpos,recipeClock,dataClock,(packet.bounds fits).1,
    fun a v h => dataStart.trans (rd a v h).1, fun a v h => dataStart.trans (wr a v h).1⟩

end CompressorRecords.ShrinkTermOnline

end

end VPVNP
end Computability
end OAI
