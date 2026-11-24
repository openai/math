import OAI.Computability.VPVNP.PairShrinkResidentSources
import OAI.Computability.VPVNP.PairShrinkPhysicalSourceBounds
import OAI.Computability.VPVNP.PairShrinkResidentTermCapture
import OAI.Computability.VPVNP.CompressorShrinkScheduledOutput
import OAI.Computability.VPVNP.CompressorShrinkTailRetention

/-!
# Capturing the resident sources from the selected shrink execution

Parts 5 through 11 preserve the old incidence words and table zero. The
resident publications lie in the old header or table five, the three scans
begin at table one, and the incidence copy writes at the successor. Thus the
old ports, ranks, dense demand pairs and selected term rows can be read in
the same snapshot as the computed slices and ordered endpoint rectangles.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkResidentSources

open BurstRAM Compression CompressorRecords CompressorRecords.DescriptorSpace
open CompressorRecords.ShrinkBlockInputs BlockPlanner SourceOnline
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {i : Fin S.steps}
variable {g w : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
variable {sel : SelectedScore.Selection B X} {base : Word w} {positions blocks t fuel cap : ℕ}

local notation "prog" => BlockProgram.script B
local notation "lay" => BlockProgram.layout B base.val positions blocks
local notation "cur" => Script.levelsPerBlock prog * t + i.val
local notation "nxt" => Script.levelsPerBlock prog * t + (i.val + 1)
local notation "tab" => (fun j : Fin 6 => tableBase lay cur j)
local notation "T" => packedIncidence lay w cur (DemandRAM.oldCount X)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "dense" => ShrinkInput.demandHead (w := w) X (tab 0)
local notation "step" => (10 : Word w)
local notation "origin" => SelectedArena.origin X term step
local notation "args" => BlockSlices.abInputs i (BlockProgram.arena B i.val 0)
  (BlockProgram.arena B i.val 1)

variable {ps₅ ps₆ ps₇ ps₈ ms ps : List (SourceOnline.Packet (BlockProgram.script B) w)}
variable {r : ShrinkOutput.TablesRun w}
local notation "allParts" => (((ps₅ ++ ps₆) ++ ps₇) ++ ps₈)

set_option maxHeartbeats 1600000 in
-- Comparing the four physical windows expands their layouts at the current and successor levels.
/-- The old incidence area and all of table zero survive the resident passes,
three output scans, successor copy, and terminal header publications. -/
theorem source_frame {m : Memory w}
    (run : ScheduledShrink.Output B i X sel base positions blocks t cap m ps₅ ps₆ ps₇ ps₈ r)
    (tail : ShrinkScheduledTail.Result B base positions blocks t cap i X (post m allParts) ms ps)
    (live : t < blocks) (size : X.positions ≤ positions) (room : endAddress lay < 2 ^ w)
    (x : ℕ) (lo : incidenceStart lay cur ≤ x) (hi : x < tab 1) :
    post (post m allParts) ps x = m x := by
  have headLo : levelStart lay cur + 66 ≤ x := lo
  have beforeNext : tab 1 ≤ levelStart lay nxt := by
    rw [show nxt = cur + 1 by omega]
    exact (Nat.le_add_right ..).trans (tableEnd_le_nextLevel lay cur (1 : Fin 6))
  have earlier := hi.trans_le beforeNext
  have firstResident : tab 1 ≤ tab 5 := (Nat.le_add_right ..).trans
    (tableEnd_le_tableBase lay cur (show (1 : Fin 6) < 5 by decide))
  have residents := run.residents.preserved x (by
    rintro (data | header)
    · exact (hi.trans_le firstResident).not_ge data.1
    · change _ ∧ x < levelStart lay cur + 36 at header
      omega)
  have scan := ShrinkOutput.scheduled_frame B i X sel base positions blocks t args
    (post m ps₅) (post m ps₅) cap r ps₈ live size room run.tables
    run.slotReports x (.inl hi) (.inl (earlier.trans_le (Nat.le_add_right ..)))
  apply (tail.old_data x (by omega) earlier).trans
  rw [post_append, run.postWidth]
  exact scan.trans residents

set_option maxHeartbeats 1600000 in
-- The dependent row types include the selected degree, numbering, and physical table heads.
/-- The actual completed shrink pass and its terminal publications establish
all resident operands in one chronological snapshot. -/
theorem Data.capture {initial : Memory w}
    {p : ShrinkBranch.Prefix X T (tab 0) fuel initial}
    (v : ShrinkBranch.Selected B X T (tab 0) step (B.shrink.selectorBits : Word w)
      fuel initial p sel)
    (run : ScheduledShrink.Output B i X sel base positions blocks t cap
      v.beforeOutput ps₅ ps₆ ps₇ ps₈ r)
    (tail : ShrinkScheduledTail.Result B base positions blocks t cap i X
      (post v.beforeOutput allParts) ms ps)
    (live : t < blocks) (size : X.positions ≤ positions) (room : endAddress lay < 2 ^ w) :
    Data B i X (S.shrink i) sel base positions blocks cur
      (post (post v.beforeOutput allParts) ps) := by
  have fits := bounds B i X base positions blocks t live size room
  have wide : (step).val = 10 := by
    have startRoom := ScorePackets.start_le_term i X (tab 0) fits.termRoom
    have lo : levelStart lay cur + 66 ≤ tab 0 := by
      change levelStart lay cur + 66 ≤ levelStart lay cur + 66 + 6 * slotCapacity lay + 0 * _
      omega
    exact Nat.mod_eq_of_lt (show 10 < 2 ^ w from by have := (term).isLt; omega)
  have termRoom : ShrinkInput.termEnd X (tab 0) (step).val < 2 ^ w := wide ▸ fits.termRoom
  have stopRoom : ShrinkInput.stop X (tab 0) < 2 ^ w := by
    unfold ShrinkInput.termEnd at termRoom
    omega
  obtain ⟨preimages, ranked⟩ := p.input.original_after_absolute p.absoluteRun stopRoom
    (fun x hx => v.lowerFrame x (hx.trans_le (ShrinkInput.range_bounds X (tab 0)).2.2.2))
  have geometry := p.input.keepAbsoluteThenTerms p.absoluteRun.frame (step).val termRoom
    v.lowerFrame
  have old : ShrinkCallHeader.OldTables X v.beforeOutput T (tab 0) :=
    ⟨preimages, ranked, geometry.incidence.actual, geometry.placement⟩
  have frame := source_frame run tail live size room
  have startLo : incidenceStart lay cur ≤ tab 0 :=
    (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have ranges := ShrinkInput.range_bounds X (tab 0)
  have denseAddr : (dense).val = ShrinkInput.stop X (tab 0) := Nat.mod_eq_of_lt stopRoom
  have sourceLo : incidenceStart lay cur ≤ (dense).val := denseAddr ▸
    startLo.trans (ranges.1.trans (ranges.2.1.trans (ranges.2.2.1.trans ranges.2.2.2)))
  have originEnd : origin ≤ tab 1 := by
    have selected := (ShrinkOutput.old_bounds i X term step).2.2
    exact (Nat.le_add_right ..).trans (selected.le.trans
      (ShrinkOutput.table_space B i X base positions blocks t live size room).abAfter)
  obtain ⟨pairs, fields⟩ := v.term_capture termRoom wide.ge
    (fun x low high => frame x (sourceLo.trans low) (high.trans_le originEnd))
  have read := tail.readbacks sel T run.readbacks live size room
  refine ⟨fits.oldTables old frame, pairs, ?_, read.hidden.directories, read.resident.directory,
    read.slices, read.ordered, ?_⟩
  · simpa only [wide] using fields
  · rw [show cur + 1 = nxt by omega]
    exact read.incidence.actual

end PairSimulation.ShrinkResidentSources

end

end VPVNP
end Computability
end OAI
