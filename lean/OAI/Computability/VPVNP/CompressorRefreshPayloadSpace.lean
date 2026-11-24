import OAI.Computability.VPVNP.CompressorBlockLevelFit

/-!
# Physical intervals of a selected refresh

The old header and the refresh scratch precede the placement writes.
Both the scratch and placement fit before the live successor header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshPayloadHistory

open BurstRAM BlockPlanner Compression DescriptorSpace PortRefresh.Allocation

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {w g : ℕ} (base : Word w) (positions blocks t : ℕ)
variable (X : State S.portExponent (S.portExponent+g))

local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "cur" => Script.levelsPerBlock (BlockProgram.script B)*t+S.steps
local notation "head" => levelStart L cur
local notation "start" => arrayBase L cur
local notation "place" => tableBase L cur (4 : Fin 6)
local notation "s" => RefreshBlockPlan.shape B
local notation "P" => plan X (S.degreeExponent 0) (PortRefresh.LevelRecipe.Shape.dH s)
  (PortRefresh.LevelRecipe.Shape.ties s) (PortRefresh.LevelRecipe.Shape.stride s) start

/-- Address bounds for preserving the selected refresh payload through its final visits. -/
structure Space : Prop where
  live : cur+1 < (L).levels
  scratch_before : (P).supply ≤ place
  header_before : head+66 ≤ start
  array_before : start ≤ levelStart L (cur+1)
  placement_before : place+3*X.positions ≤ levelStart L (cur+1)
  header_first : levelStart L 0 ≤ head
  scratch_next : (P).stop ≤ levelStart L (cur+1)

/-- The compiled block layout supplies all of the bounds at each live repetition. -/
theorem Space.ofLayout (ht : t < blocks) (size : X.positions ≤ positions)
    (room : endAddress L < 2^w) : Space B base positions blocks t X := by
  have live : cur+1 < (L).levels := by
    have h := Nat.mul_le_mul_left (S.steps+1) ht
    rw [Nat.mul_succ] at h
    change (S.steps+1)*t+S.steps+1 < 1+(S.steps+1)*blocks
    omega
  let level : Fin (L).levels := ⟨cur,by omega⟩
  obtain ⟨scratch,placement⟩ := BlockLevelFit.refresh B base.val positions blocks level rfl X size room
  change BlockLevelFit.Endpoint w L cur 0
    (plan X (S.degreeExponent 0) (s).dH (s).ties (s).stride (start+0*tableWords L)).stop at scratch
  simp only [Nat.zero_mul,Nat.add_zero] at scratch
  have supply : (P).supply ≤ (P).stop := by
    unfold Plan.stop Plan.next Plan.reverseSlot Plan.targetPort
    omega
  have before := tableEnd_le_tableBase L cur (show (0 : Fin 6) < 4 by decide)
  have zero : tableBase L cur (0 : Fin 6) = start := by simp [tableBase]
  exact ⟨live,supply.trans (scratch.within.trans before),Nat.le_add_right ..,
    zero ▸ (Nat.le_add_right _ _).trans (tableEnd_le_nextLevel L cur (0 : Fin 6)),
    placement.next,levelStart_mono L (Nat.zero_le _),scratch.next⟩

end CompressorRecords.RefreshPayloadHistory

end VPVNP
end Computability
end OAI
