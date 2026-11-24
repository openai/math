import OAI.Computability.VPVNP.CompressorShrinkBlockInputs
import OAI.Computability.VPVNP.CompressorShrinkOutputAllocation

/-!
# Reading the fixed shrinking block's live slot operands

The cyclic successor table follows the eight role words. The four
subdivision words follow the cyclic table. These expressions agree with the
allocation supplied to the native preparation and ordered-slot workers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkBlockInputs

open BurstRAM PhaseRecipe Compression SlotLevel ShrinkSlots
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (F : DescriptorSpace.Shape) (i : Fin S.steps)
variable {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g))
variable (origin slotArena : Expr) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)

local notation "ev" => Expr.eval pub state m
local notation "s" => levelShape (b := b i) X

/-- Every compiled slot head agrees with the native head used on the current selected branch. -/
theorem slotInputs_reads (role start : ℕ)
    (bases : ev (LevelFields.vertices i.val) = (Fintype.card X.Base : Word w))
    (lanes : ev (LevelFields.residualLanes i.val) = (2^g : ℕ))
    (oldArc : ev (SelectedPlan.roleBase (selectedInputs B F i origin)) = (role : Word w))
    (arena : ev slotArena = (start : Word w)) :
    SlotLevel.Recipe.Reads (slotInputs B F i origin slotArena) pub state m (Fintype.card X.Base) (2^g)
      (ShrinkOutput.heads s role start) := by
  have count : ev (newSites i) = (sites s : Word w) := by
    change ev (LevelFields.vertices i.val) * ((2^(Shrink.J (a i)) : ℕ) * ev (LevelFields.residualLanes i.val)) = _
    rw [bases,lanes,← Nat.cast_mul,← Nat.cast_mul]; rfl
  have cyclic : ev (slotArena.add (.lit 8)) = ((start+8 : ℕ) : Word w) := by
    change ev slotArena+8 = _; rw [arena,Nat.cast_add]; rfl
  have subdiv : ev ((slotArena.add (.lit 8)).add (newSites i)) = ((start+8+sites s : ℕ) : Word w) := by
    change ev (slotArena.add (.lit 8)) + ev (newSites i) = _
    rw [cyclic,count,← Nat.cast_add]
  refine ⟨bases,lanes,oldArc,arena,subdiv,cyclic,?_⟩
  change ev ((slotArena.add (.lit 8)).add (newSites i)) + 4 = ((start+8+sites s+4 : ℕ) : Word w)
  rw [subdiv]
  exact (Nat.cast_add (start+8+sites s) 4).symm

/-- These are the two persistent addresses published for subsequent endpoint lookup. -/
theorem endpoint_heads (role start : ℕ)
    (read : SlotLevel.Recipe.Reads (slotInputs B F i origin slotArena) pub state m (Fintype.card X.Base) (2^g)
      (ShrinkOutput.heads s role start)) :
    let counts := SlotLevel.Recipe.counts (slotTemplate i) (slotInputs B F i origin slotArena)
    ev counts.rows = (rowsHead s (ShrinkOutput.heads s role start) : Word w) ∧
      ev counts.inverse = (inverseHead s (ShrinkOutput.heads s role start) : Word w) := by
  intro c
  have eq := SlotLevel.Recipe.eval_counts (slotTemplate i) (slotInputs B F i origin slotArena) read
  exact ⟨congrArg SlotLevel.Recipe.Counts.rows eq,congrArg SlotLevel.Recipe.Counts.inverse eq⟩

end CompressorRecords.ShrinkBlockInputs

end VPVNP
end Computability
end OAI
