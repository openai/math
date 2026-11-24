import OAI.Computability.VPVNP.CompressorShrinkScheduledTail
import OAI.Computability.VPVNP.CompressorShrinkSlotFrame
import OAI.Computability.VPVNP.CompressorShrinkSelectedReadback
import OAI.Computability.VPVNP.CompressorShrinkTablesPhysical

/-!
# The four published addresses used to read surviving shrink operands

The absolute motif directory is the last word of the term publication.
The next level, inverse-slot table and interval bank are the first three
words of the following data publication. The latter reads the memory
left by the term publisher.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkPublishedSupplyWords

open BurstRAM Compression CompressorRecords CompressorRecords.DescriptorSpace
open CompressorRecords.BlockPlanner CompressorRecords.PhaseRecipe CompressorRecords.Schedule
open CompressorRecords.ShrinkBlockInputs CompressorRecords.SourceOnline
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (base : Word w) (positions blocks t : ℕ)

local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pub" => Ports.data (Workspace.ports (arity (Script.catalog prog)) base)
local notation "first" => Script.levelsPerBlock prog * t
local notation "cur" => first + i.val
local notation "old" => levelStart L cur
local notation "next" => levelStart L (first + (i.val + 1))
local notation "st" => (levelStart L first : Word w)
local notation "tab" => (fun j : Fin 6 ↦ tableBase L cur j)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "sh" => ShrinkSlots.levelShape (b := b i) X
local notation "role" => SelectedArena.roleBase X term (10 : Word w)
local notation "heads" => ShrinkOutput.heads sh role (tab 3)
local notation "alloc" => ShrinkSliceSweep.selectedAllocation B.shrink X sel term 10 (tab 2)
  (SlotLevel.Shape.subdivisions sh)
local notation "geometry" => BlockProgram.geometry B
local notation "arena" => BlockProgram.arena B i.val

section Words

variable (level : ℕ)
local notation "levelTab" => (fun j : Fin 6 ↦ tableBase L level j)
local notation "levelTerm" => ShrinkInput.termHead (w := w) X (levelTab 0)
local notation "levelHeads" => ShrinkOutput.heads sh (SelectedArena.roleBase X levelTerm 10)
  (levelTab 3)
local notation "levelAlloc" => ShrinkSliceSweep.selectedAllocation B.shrink X sel levelTerm 10
  (levelTab 2) (SlotLevel.Shape.subdivisions sh)

/-- Supply pointers in an absolute chronological level header. -/
structure Stored (mem : Memory w) : Prop where
  absolute : mem (levelStart L level + 39) =
    ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X (levelTab 0)) w
  successor : mem (levelStart L level + 40) = (levelStart L (level + 1) : Word w)
  inverse : mem (levelStart L level + 41) = (SlotLevel.inverseHead sh levelHeads : Word w)
  interval : mem (levelStart L level + 42) = ((levelAlloc).widthEnd : Word w)

end Words

private theorem gap : old + 66 ≤ next := by
  have size : levelHeaderWords L = 66 := rfl
  rw [show first + (i.val + 1) = cur + 1 by omega]
  simp only [levelStart, Nat.succ_mul, levelWords, size]
  omega

set_option maxHeartbeats 1500000 in
-- Reducing the three packet images unfolds the installed block and its fourteen data expressions.
/-- Recover the four published words from the three chronological packet groups
and the physical header and table pointers present at their entry. -/
theorem of_tail {cap : ℕ} {mem : Memory w} {ms ps : List (Packet prog w)}
    (T : IncidenceDirectory w) (header : ShrinkHeaderReads.Header i X T (tab 0) L first mem)
    (tables : ∀ j : Fin 6, mem (old + (60 + j.val)) = (tab j : Word w))
    (pitch : mem (pub 1 - 1).val = (levelWords L : Word w))
    (live : t < blocks) (sites : X.positions ≤ positions) (fit : endAddress L < 2 ^ w)
    (run : ShrinkScheduledTail.Result B base positions blocks t cap i X mem ms ps) :
    Stored B i X sel base positions blocks cur (post mem ps) := by
  let afterMeta := post mem ms
  have sep := gap B i base positions blocks t
  have room := PublishedHeads.level_room B base positions blocks t i.val live i.isLt.le fit
  have controls := Window.lowCells (A := prog) L base rfl rfl
    ((levelStart_mono L (Nat.zero_le _)).trans_lt fit)
  have early : (pub 1 - 1).val < old := controls.2.trans_le (levelStart_mono L (Nat.zero_le _))
  have entry : LevelFields.Entry L first pub st afterMeta :=
    ⟨rfl, (run.baseFields.outside _ (.inl (by omega)) (by omega) (by omega)).trans pitch⟩
  have saved (n : ℕ) (hn : n ≤ 65) (free : n < 15 ∨ 27 ≤ n) :
      afterMeta (old + n) = mem (old + n) :=
    run.baseFields.outside _ (by omega) (by omega) (by omega)
  have hdr : ShrinkHeaderReads.Header i X T (tab 0) L first afterMeta :=
    ⟨header.room, (saved 0 (by decide) (by decide)).trans header.vertices,
      (saved 1 (by decide) (by decide)).trans header.degree,
      (saved 2 (by decide) (by decide)).trans header.lanes,
      (saved 3 (by decide) (by decide)).trans header.residual,
      fun c ↦ (saved _ (by have := c.isLt; omega) (Or.inr (by omega))).trans (header.incidence c),
      (saved 60 (by decide) (by decide)).trans header.scratch⟩
  have table (j : Fin 6) : (arena j).eval pub st afterMeta = (tab j : Word w) := by
    have hj := j.isLt
    exact (LevelFields.eval_scalar entry i.val (60 + j.val) (by omega)).trans
      ((saved _ (by omega) (Or.inr (by omega))).trans (tables j))
  let chosen := selectedInputs B geometry i (arena 0)
  have space := ShrinkOutput.table_space B i X base positions blocks t live sites fit
  have vals := (SelectedTailPackets.header_values B i X T (tab 0) pub st afterMeta hdr entry
    space.termRoom (by omega) (fun _ ↦ True) trivial (fun _ _ ↦ trivial)).1
  have rd := hdr.reads B entry
  have roleAt := SelectedPlan.roles_head chosen X _ T term pub st afterMeta vals
  have slotAt := slotInputs_reads B geometry i X (arena 0) (arena 3) pub st afterMeta role (tab 3)
    rd.vertices rd.residual roleAt (table 3)
  have inv := (endpoint_heads B geometry i X (arena 0) (arena 3) pub st afterMeta role (tab 3)
    slotAt).2
  have intervals : (BlockSlices.intervals i (arena 2)).eval pub st afterMeta =
      ((alloc).widthEnd : Word w) := by
    change (arena 2).eval pub st afterMeta + (4 * chosen.oldSlots.eval pub st afterMeta) *
      (BlockSlices.subdivisionSum i : Word w) =
      ((tab 2 + (DemandRAM.absoluteCount X * 4) * BlockSlices.subdivisionSum i : ℕ) : Word w)
    rw [table, vals.slots, DemandRAM.count_eq X]
    push_cast
    ring
  have termRead := run.published.termGroup.source.stored (3 : Fin 4)
  have dataRead (j : Fin 14) : post mem ps (old + 40 + j.val) =
      (PublishedHeads.dataValues B i j).eval pub st afterMeta := by
    rw [run.image]
    apply (run.published.dataGroup.source.stored j).trans
    exact BlockHeadStability.shrink_data_stable B i entry room (by omega) (offset := 36) (N := 4)
      le_rfl (by decide) run.published.termGroup.source.outside j
  constructor
  · rw [run.image]
    apply (run.published.dataGroup.source.outside _ (.inl (by omega))).trans
    exact termRead.trans (ShrinkBundlePlan.head_values X rd).absoluteCD
  · rw [Nat.add_assoc first i.val 1]
    exact (dataRead 0).trans (LevelFields.eval_atLevel entry (i.val + 1))
  · exact (dataRead 1).trans inv
  · exact (dataRead 2).trans intervals

end PairSimulation.ShrinkPublishedSupplyWords

end

end VPVNP
end Computability
end OAI
