import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Memory agreement across online descriptor calls

The calendar, row recipe, launcher and closing worker call access the same
memory as the native source scans. Their writes end before the first level
header. In particular, a script can replay a source scan on the prepared
memory and carry its output into the next phase.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.OnlineFootprint

open BurstRAM DescriptorSpace BlockPlanner Schedule SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} (A : Script) (L : Layout) (base : Word w)
local notation "g₀" => arity (Script.catalog A)
local notation "P₀" => Workspace.ports (arity (Script.catalog A)) base
local notation "H" => levelStart L 0

private theorem first_level : H = directoryBase L + directoryRows L * (L.shape.arity+3) := by
  simp only [levelStart, levelsBase, Nat.zero_mul, Nat.add_zero]

variable (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base) (fit : levelStart L 0 < 2^w)

include hg hb fit in
private theorem port_bounds :
    (P₀).directory.val = directoryBase L ∧ (P₀).ordinal.val = L.base+7 ∧ (P₀).tag.val = L.base+6 ∧
      ∀ i : Fin (g₀+1), ((P₀).activeFrame+(i.val : Word w)).val < H := by
  have dir : directoryBase L = L.base+(11+g₀) := by
    rw [hg]
    simp only [directoryBase, plannerTag, frameBase]
    omega
  have before : directoryBase L ≤ H := (first_level L).symm ▸ Nat.le_add_right ..
  have atOffset (j : ℕ) (h : L.base+j ≤ directoryBase L) :
      (base+(j : Word w)).val = L.base+j := by
    have hj := (h.trans before).trans_lt fit
    rw [Fin.val_add,hb,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j < 2^w),Nat.mod_eq_of_lt hj]
  refine ⟨(atOffset (11+g₀) dir.symm.le).trans dir.symm,
    atOffset 7 (by omega),atOffset 6 (by omega),?_⟩
  intro i
  have hi := i.isLt
  have ha : L.base+(9+i.val) < directoryBase L := by omega
  change (base+9+(i.val : Word w)).val < H
  have he : base+9+(i.val : Word w) = base+((9+i.val : ℕ) : Word w) := by
    simp only [Nat.cast_add,Nat.cast_ofNat,add_assoc]
  rw [he,atOffset _ ha.le]
  exact ha.trans_le before

include hg hb fit in
private theorem tag_before : (P₀).tag.val < H := by
  rw [(port_bounds A L base hg hb fit).2.2.1,first_level]
  simp only [directoryBase, plannerTag, frameBase]
  omega

include hg hb fit in
/-- The current row's exclusive end is at most the first level address,
including the final allocated row. -/
theorem row_bound (m : Memory w) (active : (m (P₀).ordinal.val).val < directoryRows L) :
    (Controller.rowBase g₀ (P₀).data m).val + (g₀+3) ≤ H := by
  have dir := (port_bounds A L base hg hb fit).1
  have end_le : (P₀).directory.val + (m (P₀).ordinal.val).val*(g₀+3) + (g₀+3) ≤ H := by
    rw [dir,first_level,← hg, Nat.add_assoc,← Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ active) _
  have hval := Directory.rowBase_val A.catalog P₀ m (by omega)
  change (Directory.rowBase A.catalog P₀ m).val + (g₀+3) ≤ H
  rw [hval]
  exact end_le

include hg hb fit in
theorem calendar (m : Memory w) (j : Fin A.size) :
    Agree (H ≤ ·) m (after m (Online.calendarReport A.plan P₀ m j).events) := by
  rw [(Online.calendar_effect A.plan P₀ m j).2.1]
  intro a ha
  have hn := ne_of_gt ((tag_before A L base hg hb fit).trans_le ha)
  simp [writeMemory,hn]

include hg hb fit in
theorem recipe (j : Fin A.size) (s : Word w) (m : Memory w)
    (active : (m (P₀).ordinal.val).val < directoryRows L) :
    Agree (H ≤ ·) m (after m (Online.recipeReport A.plan P₀ j s m).events) := by
  let R := (A.phase j).recipe
  have bound : (R.address (P₀).data s m).val + (g₀+3) ≤ H := by
    rw [PhaseRecipe.recipe_address]
    exact row_bound A L base hg hb fit m active
  rw [(Online.recipe_effect A.plan P₀ j s m).2.1]
  intro a ha
  have hn := ne_of_gt ((tag_before A L base hg hb fit).trans_le ha)
  change m a = writeMemory (Greedy.writeRow m (R.address (P₀).data s m) (R.words (P₀).data s m)) (P₀).tag 0 a
  rw [writeMemory,ite_eq_right hn,← RowRecipe.after_row]
  exact (RowRecipe.row_outside R (P₀).data s m (bound.trans fit.le) a (.inr (bound.trans ha))).symm

include hg hb fit in
theorem launch (m : Memory w) :
    Agree (H ≤ ·) m (after m (Online.launchReport A.catalog A.size P₀ m).events) := by
  rw [(Online.launch_effect (C := A.catalog) (initial := A.initial.length)
    (phases := A.block.length) P₀ m).2.1]
  intro a ha
  obtain ⟨_,ho,_,hf⟩ := port_bounds A L base hg hb fit
  have ord : (P₀).ordinal.val < H := by
    rw [ho,first_level]
    simp only [directoryBase, plannerTag, frameBase]
    omega
  exact (Controller.after_row_outside g₀ (P₀).data m a (ne_of_gt (ord.trans_le ha))
    (ne_of_gt ((tag_before A L base hg hb fit).trans_le ha)) (fun i => ne_of_gt ((hf i).trans_le ha))).symm

include hg hb fit in
theorem worker_close (i : Fin A.size) (m : Memory w) :
    Agree (H ≤ ·) m (after m (Online.stopReport A.catalog A.size P₀ i m).events) := by
  rw [(Online.stop_effect (C := A.catalog) (initial := A.initial.length)
    (phases := A.block.length) P₀ i m).2.1]
  intro a ha
  have hn := ne_of_gt ((tag_before A L base hg hb fit).trans_le ha)
  simp [writeMemory,hn]

include hg hb fit in
/-- The source worker enters with the same contents at every level address
as at entry to the calendar. -/
theorem prepared (m : Memory w) (j : Fin A.size) (active : (m (P₀).ordinal.val).val < directoryRows L) :
    Agree (H ≤ ·) m (Directory.prepared A.catalog P₀ (Online.rowInput A.plan P₀ m j)) := by
  let pre := Online.calendarMemory (d := A.size) P₀ m j
  let state := LevelCalendar.header (Online.calendar A.plan) (P₀).data m
  let input := Online.rowInput A.plan P₀ m j
  obtain ⟨_,ho,ht,_⟩ := port_bounds A L base hg hb fit
  have diff : (P₀).ordinal.val ≠ (P₀).tag.val := by omega
  have active' : (pre (P₀).ordinal.val).val < directoryRows L := by
    simpa only [pre,Online.calendarMemory,writeMemory,diff,↓reduceIte] using active
  have hc := calendar A L base hg hb fit m j
  rw [(Online.calendar_effect A.plan P₀ m j).2.1] at hc
  have hr := recipe A L base hg hb fit j state pre active'
  rw [(Online.recipe_effect A.plan P₀ j state pre).2.1] at hr
  have hl := launch A L base hg hb fit input
  rw [(Online.launch_effect (C := A.catalog) (initial := A.initial.length)
    (phases := A.block.length) P₀ input).2.1] at hl
  exact fun a ha => (hc a ha).trans ((hr a ha).trans (hl a ha))

/-- The three actual linked reports have the prepared memory as their
effect, including the parameter snapshot and the ordinal increment. -/
theorem preparation_effect (m : Memory w) (j : Fin A.size) :
    after m (eventLog (Online.preparation A.plan P₀ m j)) =
      Directory.prepared A.catalog P₀ (Online.rowInput A.plan P₀ m j) := by
  let pre := Online.calendarMemory (d := A.size) P₀ m j
  let state := LevelCalendar.header (Online.calendar A.plan) (P₀).data m
  let input := Online.rowInput A.plan P₀ m j
  have hc : after m (Online.calendarReport A.plan P₀ m j).events = pre :=
    (Online.calendar_effect A.plan P₀ m j).2.1
  have hr : after pre (Online.recipeReport A.plan P₀ j state pre).events = input :=
    (Online.recipe_effect A.plan P₀ j state pre).2.1
  simp only [Online.preparation,eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    after,List.foldl_append]
  change after (after (after m _) _) (Online.launchReport A.catalog A.size P₀ input).events = _
  rw [hc,hr]
  exact (Online.launch_effect (C := A.catalog) (initial := A.initial.length)
    (phases := A.block.length) P₀ input).2.1

include hg hb fit in
/-- The worker's closing transfer passes its data output to the next calendar. -/
theorem post (row : Directory.Row A.size w) :
    Agree (H ≤ ·) (row.endMemory A.catalog P₀) (Online.post A.catalog A.size P₀ row) := by
  have h := worker_close A L base hg hb fit row.worker (row.endMemory A.catalog P₀)
  rw [(Online.stop_effect (C := A.catalog) (initial := A.initial.length)
    (phases := A.block.length) P₀ row.worker _).2.1] at h
  exact h

include hg hb fit in
/-- A source packet computed on its own input replays on the launched
worker's memory. Its output agrees with the memory of the next calendar. -/
theorem replay (raw m : Memory w) (j : Fin A.size) (row : Directory.Row A.size w)
    (active : (m (P₀).ordinal.val).val < directoryRows L)
    (input : row.input = Online.rowInput A.plan P₀ m j)
    (agree : Agree (H ≤ ·) raw m) (reads : Reads (H ≤ ·) (eventLog row.reports))
    (run : runSegment ((A.catalog row.worker).table.instantiate w
      (Directory.words A.catalog P₀ row.worker row.input)).program row.fuel
      (some (Directory.start A.catalog P₀ row.input)) raw row.choices = some row.reports) :
    runSegment ((A.catalog row.worker).table.instantiate w
      (Directory.words A.catalog P₀ row.worker row.input)).program row.fuel
      (some (Directory.start A.catalog P₀ row.input)) (row.dataMemory A.catalog P₀)
      row.choices = some row.reports ∧
      Agree (H ≤ ·) (after raw (eventLog row.reports)) (Online.post A.catalog A.size P₀ row) := by
  have entry : Agree (H ≤ ·) raw (row.dataMemory A.catalog P₀) := by
    rw [Directory.Row.dataMemory,input]
    exact fun a ha => (agree a ha).trans (prepared A L base hg hb fit m j active a ha)
  obtain ⟨run',out⟩ := SourceTransport.segment run entry reads
  exact ⟨run', fun a ha => (out a ha).trans (post A L base hg hb fit row a ha)⟩

end CompressorRecords.OnlineFootprint

end VPVNP
end Computability
end OAI
