import OAI.Computability.VPVNP.CompressorPublishedHeadWindows
import OAI.Computability.VPVNP.CompressorBlockHeadReads
import OAI.Computability.VPVNP.CompressorSourceGroups

/-! # The four DFS publication windows of a compression block

A shrinking block publishes four term operands and fourteen addresses.
The refresh publishes four term operands and the next level address.
Every group runs at its occurrence in the global online script.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.PublishedHeads

open BurstRAM DescriptorSpace PhaseRecipe BlockPlanner Schedule SourceTransport Compression
open scoped Fin.CommRing

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (base : Word w) (positions blocks t cap : ℕ) (m : Memory w)
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog prog)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first" => Script.levelsPerBlock prog * t
local notation "st" => (levelStart L (first) : Word w)

/-- The controller words on entry to a publication group. -/
structure Ready : Prop where
  block : t < blocks
  room : endAddress L < 2^w
  rows : m (pt).rows.val = (directoryRows L : Word w)
  pitch : m (pub 1-1).val = (levelWords L : Word w)
  clock : SourceOnline.scanCap prog 7 ≤ cap

variable {B base positions blocks t cap m}

private theorem Ready.pitch_before (h : Ready B base positions blocks t cap m) (step : ℕ) :
    (pub 1-1).val < levelStart L (first+step)+36 := by
  have fit := (levelStart_mono L (Nat.zero_le _)).trans_lt h.room
  have controls := Window.lowCells (A:=prog) L base rfl rfl fit
  exact controls.2.trans_le ((levelStart_mono L (Nat.zero_le _)).trans (Nat.le_add_right ..))

private theorem Ready.entry (h : Ready B base positions blocks t cap m) :
    LevelFields.Entry L (first) pub st m := ⟨rfl,h.pitch⟩

private theorem Ready.framedEntry (h : Ready B base positions blocks t cap m) {mem : Memory w}
    {step offset n : ℕ} (lo : 36 ≤ offset)
    (frame : Agree (Outside (levelStart L (first+step)+offset) n) mem m) :
    LevelFields.Entry L (first) pub st mem :=
  ⟨rfl,(frame _ (.inl ((h.pitch_before step).trans_le (Nat.add_le_add_left lo _)))).trans h.pitch⟩

variable (B) (i : Fin S.steps)

/-- The fourteen address expressions published for the selected shrinking reader, computed from
the four designated scratch tables. -/
def dataValues : Fin 14 → Expr := BlockDataHeads.values B (BlockProgram.geometry B) i
  (BlockProgram.arena B i.val 0) (BlockProgram.arena B i.val 1) (BlockProgram.arena B i.val 2) (BlockProgram.arena B i.val 3)

private abbrev chosen := ShrinkBlockInputs.selectedInputs B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0)

/-- The term group uses the bit in the selected layout's score table. -/
theorem shrink_terms_window (h : Ready B base positions blocks t cap m)
    (score : levelStart L (first+i.val)+54 ≤ ((SelectedPlan.layoutCell (chosen B i)).eval pub st m).val) :
    Installed B base positions blocks t i.val 36 (BlockHeadStability.shrinkTerms B i) (BlockGroups.shrink B i 10) cap m := by
  have room := level_room B base positions blocks t i.val h.block i.isLt.le h.room
  have pitch := h.pitch_before i.val
  apply install _ _ _ _ _ _ _ _ _ _ _ h.block h.room i.isLt.le (by decide) h.rows h.pitch h.clock
  · exact fun _ frame j ↦ BlockHeadStability.shrink_term_stable B i h.entry room pitch le_rfl (by decide) score frame j
  · intro mem frame j
    apply BlockHeadReads.shrink_terms B i (h.framedEntry le_rfl frame) room _ j
    rw [BlockHeadStability.shrink_layoutCell_stable B i h.entry room pitch le_rfl (by decide) frame]
    exact ((levelStart_mono L (Nat.zero_le _)).trans (Nat.le_add_right ..)).trans score

theorem shrink_data_window (h : Ready B base positions blocks t cap m) :
    Installed B base positions blocks t i.val 40 (dataValues B i) (BlockGroups.shrink B i 11) cap m := by
  have room := level_room B base positions blocks t i.val h.block i.isLt.le h.room
  apply install _ _ _ _ _ _ _ _ _ _ _ h.block h.room i.isLt.le (by decide) h.rows h.pitch h.clock
  · exact fun _ frame j ↦ BlockHeadStability.shrink_data_stable B i h.entry room (h.pitch_before i.val) (by decide) (by decide) frame j
  · exact fun _ frame j ↦ BlockHeadReads.shrink_data B i (h.framedEntry (by decide) frame) room j

theorem refresh_terms_window (h : Ready B base positions blocks t cap m) :
    Installed B base positions blocks t S.steps 36 (BlockHeadStability.refreshTerms B) (BlockGroups.refresh B 5) cap m := by
  have room := level_room B base positions blocks t S.steps h.block le_rfl h.room
  apply install _ _ _ _ _ _ _ _ _ _ _ h.block h.room le_rfl (by decide) h.rows h.pitch h.clock
  · exact fun _ frame j ↦ BlockHeadStability.refresh_term_stable B h.entry room (h.pitch_before S.steps) le_rfl (by decide) frame j
  · exact fun _ frame j ↦ BlockHeadReads.refresh_terms B (h.framedEntry le_rfl frame) room j

theorem refresh_next_window (h : Ready B base positions blocks t cap m) :
    Installed B base positions blocks t S.steps 40 (fun _ : Fin 1 ↦ LevelFields.atLevel (S.steps+1))
      (BlockGroups.refresh B 6) cap m := by
  apply install _ _ _ _ _ _ _ _ _ _ _ h.block h.room le_rfl (by decide) h.rows h.pitch h.clock
  · exact fun _ frame _ ↦ BlockHeadStability.next_level_stable h.entry (h.pitch_before S.steps) (by decide) frame
  · exact fun _ _ _ ↦ BlockHeadReads.level (S.steps+1)

variable {B}

theorem Ready.after_publication {N step offset : ℕ} {rhs : Fin N → Expr} {W : Window prog (fieldVisits step offset rhs)}
    (h : Ready B base positions blocks t cap m) (group : Installed B base positions blocks t step offset rhs W cap m) :
    Ready B base positions blocks t cap (image pub st m (levelStart L (first+step)+offset) rhs) := by
  have fit := (levelStart_mono L (Nat.zero_le _)).trans_lt h.room
  have controls := Window.lowCells (A:=prog) L base rfl rfl fit
  have bound : levelStart L 0 ≤ levelStart L (first+step)+offset :=
    (levelStart_mono L (Nat.zero_le _)).trans (Nat.le_add_right ..)
  exact ⟨h.block,h.room,(group.source.outside _ (.inl (controls.1.trans_le bound))).trans h.rows,
    (group.source.outside _ (.inl (controls.2.trans_le bound))).trans h.pitch,h.clock⟩

end CompressorRecords.PublishedHeads

end

end VPVNP
end Computability
end OAI
