import OAI.Computability.VPVNP.CompressorBlockMetadataWindows
import OAI.Computability.VPVNP.CompressorShrinkSelectedReadback

/-! # Reading the installed DFS operands of a selected shrinking substep -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockMetadata

open BurstRAM Compression DescriptorSpace BlockPlanner Schedule ShrinkBlockInputs
open scoped Fin.CommRing

open private roleEnd_value rows_value from OAI.Computability.VPVNP.CompressorShrinkSelectedTailPackets

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
    {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)

local notation "term" => ShrinkInput.termHead (w := w) X start

/-- Physical child-directory bases used by the selected placement and its
append worker. -/
def shrinkPlacement : Placement := ⟨ShrinkPreimages.newCount X,
  SelectedArena.placementBase X term 10,SelectedFinish.countStart X term 10,
  SelectedFinish.rowStart X term 10,ShrinkPreimages.capacity (a i)⟩

variable (base : Word w) (positions blocks t : ℕ)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Ports.data pt
local notation "first" => Script.levelsPerBlock scr*t
local notation "st" => (levelStart L first : Word w)
local notation "I" => ShrinkBlockInputs.selectedInputs B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0)
local notation "pre" => ShrinkInput.placementBank X T start

/-- The physical owner, count and rows of the new node family are the
same native arrays filled by the selected shrinking passes. -/
theorem Published.shrink_payload {m : Memory w} {rs : List (Report w)}
    (P : Published B base positions blocks t i.val .shrink (shrinkFields B i) m (ShrinkPreimages.oldCount X) rs)
    (header : ShrinkHeaderReads.Header i X T start L first m)
    (entry : LevelFields.Entry L first pub st m) (termFits : ShrinkInput.termEnd X start 10 < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (n : ℕ) (nCell : m (levelStart L 0+29) = (n : Word w)) (j : Fin 12) :
    after m (eventLog rs) (levelStart L (first+i.val)+15+j.val) =
      (BlockMetadata.payload B.recordLimit (slotDegree S) (2^(a i)) n T.actualIn.val T.width.val
        (ShrinkPreimages.oldCount X) (shrinkPlacement (w := w) i X start) j : Word w) := by
  have lo := levelStart_mono L (Nat.zero_le (first+i.val))
  have ten : 10 < 2^w := by have := header.room; omega
  have read := (SelectedTailPackets.header_values B i X T start pub st m header entry termFits ten
    (fun _ => True) trivial (fun _ _ => trivial)).1
  have basic := header.reads B entry
  have initial : BlockHeaderPlan.firstHeader.eval pub st m = (levelStart L 0 : Word w) :=
    BlockHeaderPlan.firstHeader_eval L base m st (Fin.cast_val_eq_self _).symm rows
  have stride : ((I).termStride : Word w) = 10 := by
    change ((10 : ℕ) : Word w) = 10
    simp only [Nat.cast_ofNat]
  have owner : (SelectedPlan.placementColumn I 0).eval pub st m =
      (SelectedArena.placementBase X term 10 : Word w) := by
    have h := SelectedPlan.placement_column I X pre T term pub st m read 0
    simpa only [SelectedArena.placementWord,Fin.val_zero,Nat.zero_mul,Nat.add_zero,stride,Fin.ofNat_eq_cast] using h
  have count := roleEnd_value I X term pre T pub st m read
  have row := rows_value I X term pre T pub st m read
  rw [stride] at count row
  have placement : (shrinkPlacement (w := w) i X start).reads (shrinkFields B i) pub st m :=
    ⟨read.nextSites,owner,count.trans (Fin.ofNat_eq_cast _ _),row.trans (Fin.ofNat_eq_cast _ _),rfl⟩
  have hin : (LevelFields.incidence (L).shape i.val 4).eval pub st m = (T.actualIn.val : Word w) :=
    (basic.incidence 4).trans (Fin.cast_val_eq_self _).symm
  have hwid : (LevelFields.incidence (L).shape i.val 5).eval pub st m = (T.width.val : Word w) :=
    (basic.incidence 5).trans (Fin.cast_val_eq_self _).symm
  exact (P.payload j).trans (field_values B.recordLimit (slotDegree S) (shrinkFields B i)
    (shrinkPlacement (w := w) i X start) initial (by have := header.room; omega) nCell basic.degree read.sites
    hin hwid placement j)

end CompressorRecords.BlockMetadata

end

end VPVNP
end Computability
end OAI
