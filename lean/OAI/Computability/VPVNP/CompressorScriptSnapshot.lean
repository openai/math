import OAI.Computability.VPVNP.CompressorOnlineFootprint

/-! # The operands loaded by each actual compressor-script visit

The calendar and recipe compute an address and all public worker operands in
the current memory. The launcher copies these operands to the active frame,
increments the ordinal and preserves the row count. All addresses are derived
from the declared workspace layout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockPlanner.Script

open BurstRAM DescriptorSpace Schedule
open scoped Fin.CommRing

variable {w : ℕ} (A : Script) (L : Layout) (base : Word w)
local notation "g₀" => arity A.catalog
local notation "P₀" => Workspace.ports g₀ base

private theorem field_addresses (g : ℕ) (base : Word w) (fit : base.val + (11+g) < 2^w) :
    let p := Workspace.ports g base
    p.tag.val = base.val+6 ∧ p.ordinal.val = base.val+7 ∧ p.rows.val = base.val+8 ∧
      p.directory.val = base.val+(11+g) ∧
      ∀ i : Fin (g+1), (p.activeFrame+(i.val : Word w)).val = base.val+(9+i.val) := by
  intro p
  have addAt (j : ℕ) (hj : j ≤ 11+g) : (base+(j : Word w)).val = base.val+j := by
    rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j < 2^w),Nat.mod_eq_of_lt (by omega)]
  refine ⟨addAt 6 (by omega),addAt 7 (by omega),addAt 8 (by omega),addAt _ le_rfl,fun i => ?_⟩
  change (base+9+(i.val : Word w)).val = _
  rw [show base+9+(i.val : Word w) = base+((9+i.val : ℕ) : Word w) by simp [Nat.cast_add,add_assoc]]
  exact addAt _ (by have := i.isLt; omega)

/-- Compute the level header used by the script recipe from the calendar and the current
memory. -/
def recipeState (m : Memory w) := LevelCalendar.header (Online.calendar A.plan) (P₀).data m

/-- Evaluate a recipe expression at a script occurrence using its level header and calendar
memory. -/
def operand (m : Memory w) (j : Fin A.size) (x : PhaseRecipe.Expr) : Word w :=
  x.eval (P₀).data (recipeState A base m) (Online.calendarMemory (d := A.size) P₀ m j)

/-- The row directory, active frame, and controller counter properties all
hold on the actual output of the calendar and its selected recipe. -/
theorem snapshot (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base)
    (fit : levelStart L 0 < 2^w) (m : Memory w) (j : Fin A.size)
    (room : (m (P₀).ordinal.val).val < directoryRows L) (live : m (P₀).ordinal.val < m (P₀).rows.val) :
    let entry := Online.rowInput A.plan P₀ m j
    let prepared := Directory.prepared A.catalog P₀ entry
    let visit := A.visit j
    entry (P₀).ordinal.val = m (P₀).ordinal.val ∧ entry (P₀).rows.val = m (P₀).rows.val ∧
      entry (P₀).tag.val = 0 ∧
      Directory.start A.catalog P₀ entry = operand A base m j visit.initial ∧
      Directory.bound A.catalog P₀ entry = operand A base m j visit.stop ∧
      Directory.words A.catalog P₀ j entry = (fun i => operand A base m j (visit.params i)) ∧
      Ready A.catalog j P₀ (fun i => operand A base m j (visit.params i)) (operand A base m j visit.stop) prepared ∧
      (prepared (P₀).ordinal.val).val = (m (P₀).ordinal.val).val+1 ∧
      prepared (P₀).rows.val = m (P₀).rows.val := by
  intro entry prepared visit
  have hdir : directoryBase L = base.val+(11+g₀) := by
    rw [hg,hb]
    simp only [directoryBase,plannerTag,frameBase]
    omega
  have hend : levelStart L 0 = directoryBase L + directoryRows L*(g₀+3) := by
    simp [levelStart,levelsBase,hg]
  have hfit : base.val + (11+g₀) < 2^w := by rw [← hdir]; omega
  obtain ⟨tag,ord,total,dir,bank⟩ := field_addresses g₀ base hfit
  have ot : (P₀).ordinal ≠ (P₀).tag := fun h => by have := congrArg Fin.val h; omega
  have tt : (P₀).rows ≠ (P₀).tag := fun h => by have := congrArg Fin.val h; omega
  have frame : Directory.FrameFits A.catalog P₀ := by
    refine ⟨by omega,fun i => ?_⟩
    have h := bank i
    constructor <;> intro he <;> have hh := congrArg Fin.val he <;> omega
  have high := OnlineFootprint.row_bound A L base hg hb fit m room
  have addrFit : (P₀).directory.val + (m (P₀).ordinal.val).val*(g₀+3) < 2^w := by
    have h := Nat.mul_le_mul_right (g₀+3) room
    rw [Nat.succ_mul] at h
    omega
  have addr := Directory.rowBase_val A.catalog P₀ m addrFit
  have away (k : Word w) (h : k ∈ [(P₀).tag,(P₀).ordinal,(P₀).rows]) :
      k.val < (Directory.rowBase A.catalog P₀ m).val ∨ (Directory.rowBase A.catalog P₀ m).val+(g₀+3) ≤ k.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl <;> exact Or.inl (by omega)
  let st := operand A base m j visit.initial
  let stop := operand A base m j visit.stop
  let params := fun i => operand A base m j ((A.phase j).params i)
  have src := Online.computed_ready A.plan P₀ m j j st stop params frame ot tt
    (PhaseRecipe.recipe_address (A.phase j) ..) (PhaseRecipe.recipe_words (A.phase j) ..) (high.trans fit.le) away
  obtain ⟨eo,er,es,ready⟩ := src
  have eqParams : (fun u => params (Fin.castLE (params_le_arity A.catalog j) u)) =
      (fun i => operand A base m j (visit.params i)) := by
    funext i
    exact congrArg (operand A base m j) (A.phase_param j i)
  rw [eqParams] at ready
  have rt : entry (Directory.rowBase A.catalog P₀ entry).val = LiveStageLink.tagWord w j.succ :=
    (Controller.after_row_tag g₀ (P₀).data entry).symm.trans ready.1
  have actual := Directory.ready A.catalog P₀ entry j frame rt
  have entryLive : entry (P₀).ordinal.val < entry (P₀).rows.val := by
    rw [show entry (P₀).ordinal.val = _ from eo, show entry (P₀).rows.val = _ from er]
    exact live
  refine ⟨eo,er,by simp [entry,Online.rowInput,writeMemory],es,
    actual.2.1.symm.trans ready.2.1,actual.2.2.symm.trans ready.2.2,ready,?_,?_⟩
  · exact (Controller.after_row_ordinal_val g₀ (P₀).data entry ot entryLive).trans
      (congrArg (fun x : Word w => x.val+1) eo)
  · apply Eq.trans _ er
    apply Controller.after_row_outside g₀ (P₀).data entry
    · change (P₀).rows.val ≠ (P₀).ordinal.val; omega
    · exact Fin.val_ne_of_ne tt
    · intro i
      have h := bank i
      change (P₀).rows.val ≠ ((P₀).activeFrame+(i.val : Word w)).val
      omega

end CompressorRecords.BlockPlanner.Script

end VPVNP
end Computability
end OAI
