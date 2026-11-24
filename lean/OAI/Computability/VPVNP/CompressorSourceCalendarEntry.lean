import OAI.Computability.VPVNP.CompressorSourceSequence
import OAI.Computability.VPVNP.CompressorRecordsLevelFields

/-!
# The level header seen by a repeated online recipe

At a live calendar ordinal the row counter and pitch identify the first
level of the current block. Writing the recipe tag preserves that pitch
and all source data in the level arena.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceOnline

open BurstRAM BlockPlanner Schedule DescriptorSpace SourceTransport
open scoped Fin.CommRing
open private field_addresses from OAI.Computability.VPVNP.CompressorScriptSnapshot

variable {w : ℕ} (A : Script) (L : Layout) (base : Word w)
local notation "g" => arity A.catalog
local notation "pt" => Workspace.ports (arity A.catalog) base
local notation "H" => levelStart L 0

theorem calendar_entry (arityFit : g = L.shape.arity) (baseFit : base.val = L.base) (fit : H < 2^w)
    (m : Memory w) (j : Fin A.size) (block : ℕ)
    (level : (Online.calendar A.plan).level (m (pt).ordinal.val).val = block)
    (total : (m (pt).rows.val).val = directoryRows L)
    (pitch : m ((pt).directory-1).val = (levelWords L : Word w)) :
    let pre := Online.calendarMemory (d := A.size) pt m j
    LevelFields.Entry L (A.levelsPerBlock*block) (pt).data (A.recipeState base m) pre ∧ Agree (H ≤ ·) m pre := by
  intro pre
  have top : H = base.val+(11+g)+directoryRows L*(g+3) := by
    simp only [levelStart,levelsBase,directoryBase,plannerTag,frameBase,Nat.zero_mul,Nat.add_zero,baseFit,arityFit]
    omega
  have dirRoom : base.val+(11+g) < 2^w := by omega
  obtain ⟨tagAt,_,_,dirAt,_⟩ := field_addresses g base dirRoom
  have dir : (pt).data 1 = (directoryBase L : Word w) := by
    apply Fin.ext
    change (pt).directory.val = (directoryBase L)%(2^w)
    have head : directoryBase L = base.val+(11+g) := by unfold directoryBase plannerTag frameBase; omega
    rw [dirAt,head,Nat.mod_eq_of_lt dirRoom]
  have rows : m ((pt).data 3).val = (directoryRows L : Word w) := by
    apply Fin.ext
    rw [Fin.val_natCast,← total,Nat.mod_eq_of_lt (m (pt).rows.val).isLt]; rfl
  have original := LevelFields.eval_calendar_entry (Online.calendar A.plan) (pt).data m L dir
    (show (Online.calendar A.plan).rowPitch = L.shape.arity+3 from congrArg (·+3) arityFit) rows pitch
  have first : (Online.calendar A.plan).levelsPerBlock * (Online.calendar A.plan).level (m ((pt).data 2).val).val =
      A.levelsPerBlock*block := congrArg (A.levelsPerBlock*·) level
  rw [first] at original
  have gapVal : ((pt).directory-1).val = base.val+(10+g) := by
    have one : (1 : Word w).val = 1 := by
      change 1 % (2^w) = 1
      exact Nat.mod_eq_of_lt (show 1 < 2^w by omega)
    have le : (1 : Word w) ≤ (pt).directory := Fin.le_def.mpr (by rw [one,dirAt]; omega)
    rw [Fin.sub_val_of_le le,dirAt,one]; omega
  have tagNe : ((pt).directory-1).val ≠ (pt).tag.val := by omega
  refine ⟨⟨original.pointer,?_⟩,fun x hx => ?_⟩
  · change writeMemory m (pt).tag _ ((pt).directory-1).val = _
    rw [writeMemory,ite_eq_right tagNe]; exact pitch
  · change m x = writeMemory m (pt).tag _ x
    rw [writeMemory,ite_eq_right (by omega : x ≠ (pt).tag.val)]

end CompressorRecords.SourceOnline

end VPVNP
end Computability
end OAI
