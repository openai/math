import OAI.Computability.VPVNP.CompressorBlockLevelFit
import OAI.Computability.VPVNP.CompressorShrinkAllocatedTables
import OAI.Computability.VPVNP.CompressorSlotCoreAccess

/-! # Word and incidence capacity for a physical shrinking slot workspace

The selected role columns occupy table zero. Table two holds the balanced
subdivisions and their interval records. Table three holds the slot workspace.
The available address range also bounds the lane, tag, subdivision and degree
words used by the slot workers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotCalendar

open BurstRAM Compression DescriptorSpace ShrinkBlockInputs ShrinkSlots SlotLevel
open scoped Fin.CommRing
open private packed_le absolute_eq from OAI.Computability.VPVNP.CompressorShrinkLevelSpace

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
variable (base positions blocks : ℕ) {L : Layout} (level : Fin L.levels)
local notation "tab" => BlockLevelFit.tableStart L level.val
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "step" => (10 : Word w)
local notation "role" => SelectedArena.roleBase X term step
local notation "sh" => levelShape (b := b i) X
local notation "h" => ShrinkOutput.heads sh role (tab 3)

theorem physical_space (physical : L = BlockProgram.layout B base positions blocks)
    (size : X.positions ≤ positions) (fit : endAddress L < 2 ^ w) :
    Build.Space sh h (tab 2) w ∧ actualCount sh ≤ slotCapacity L ∧
      (ShrinkOutput.slotHeads (b := b i) X (term).val (step).val role (tab 2)).role ≤ tab 3 ∧
      ShrinkOutput.widthBase X (term).val (step).val role (tab 2) = tab 2 := by
  have ends := BlockLevelFit.shrink B base positions blocks level physical i X size fit
  have zeroBefore : tab 0 + tableWords L ≤ tab 2 := by unfold BlockLevelFit.tableStart; omega
  have twoBefore : tab 2 + tableWords L ≤ tab 3 := by unfold BlockLevelFit.tableStart; omega
  have retained : SelectedFinish.stop X term step ≤ tab 2 := ends.2.2.1.within.trans zeroBefore
  have widthEq := ShrinkOutput.width_at_eq i X term step (tab 2) retained
  have gap : ShrinkOutput.slotsBase X (tab 2) sh ≤ tab 3 :=
    ends.2.2.2.2.2.1.within.trans twoBefore
  have slotRoom : finish sh h < 2^w := ends.2.2.2.2.2.2.1.word
  have sumRoom : ShrinkOutput.slotsBase X (tab 2) sh < 2^w := ends.2.2.2.2.2.1.word
  have roleBound := (ShrinkOutput.old_bounds i X term step).2.1.trans retained
  have widthBound : tab 2 + (ShrinkOutput.absoluteCount X * 4) * (∑ t, (sh).subdivisions t) ≤
      ShrinkOutput.slotsBase X (tab 2) sh := Nat.le_add_right ..
  have absolutePos : 0 < ShrinkOutput.absoluteCount X := by
    rw [absolute_eq X]
    exact Nat.mul_pos X.positions_pos (Nat.two_pow_pos _)
  have profile : (∑ t, (sh).subdivisions t) < 2 ^ w :=
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos absolutePos (by decide : 0 < 4))).trans_lt
      ((Nat.le_add_left ..).trans_lt (widthBound.trans_lt sumRoom))
  have tagPos : 0 < (sh).tags := Nat.two_pow_pos _
  have lanePos : 0 < (sh).lanes := Nat.two_pow_pos _
  have basePos : 0 < (sh).bases := Fintype.card_pos
  have degPos : 0 < (sh).newDegree := Nat.two_pow_pos _
  have sitePos : 0 < sites sh := Nat.mul_pos basePos (Nat.mul_pos tagPos lanePos)
  have countRoom : actualCount sh < 2^w := (Nat.le_add_left ..).trans_lt slotRoom
  have siteRoom : sites sh < 2^w := (Nat.le_mul_of_pos_right _ degPos).trans_lt countRoom
  have tagsLanes : (sh).tags * (sh).lanes < 2^w := (Nat.le_mul_of_pos_left _ basePos).trans_lt siteRoom
  have degreeBound : 2^(b i) ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j)
      (Finset.mem_univ i.succ)).trans (le_max_right ..)
  refine ⟨⟨?_,widthBound.trans gap,le_rfl,le_rfl,le_rfl,slotRoom,
    (Nat.le_mul_of_pos_left _ tagPos).trans_lt tagsLanes,
    (Nat.le_mul_of_pos_right _ lanePos).trans_lt tagsLanes,profile,
    (Nat.le_mul_of_pos_left _ sitePos).trans_lt countRoom⟩,?_,?_,widthEq⟩
  · exact roleBound.trans ((Nat.le_add_right ..).trans twoBefore)
  · have capacity : slotCapacity L = positions * slotDegree S := physical ▸ rfl
    rw [capacity]
    exact Nat.mul_le_mul ((packed_le X).trans size) degreeBound
  · change ShrinkOutput.slotsBase X (ShrinkOutput.widthBase X (term).val (step).val role (tab 2)) sh ≤ _
    rw [widthEq]; exact gap

end CompressorRecords.ShrinkSlotCalendar

end VPVNP
end Computability
end OAI
