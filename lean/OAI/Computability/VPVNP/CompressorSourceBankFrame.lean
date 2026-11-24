import OAI.Computability.VPVNP.CompressorScriptSnapshot
import OAI.Computability.VPVNP.CompressorOnlinePeel
import OAI.Computability.VPVNP.CompressorSourceWalk
import OAI.Computability.VPVNP.CompressorRecordsOnlineWorkspace

/-! # The physical pointer bank across all calls of a descriptor row

The calendar tag, ordinal, active frame, recipe row and data workspace lie
above the six external pointer cells. Each original data call is charged its
own writes. Each scheduler call has its concrete memory effect. Consequently
the framing reads on every intervening call see the same pointers, and words
preceding the workspace, including the virtual header span, survive the row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceBankFrame
open BurstRAM DescriptorSpace BlockPlanner Schedule SourceTransport
open scoped Fin.CommRing
open private field_addresses from OAI.Computability.VPVNP.CompressorScriptSnapshot
open private workerRows_after from OAI.Computability.VPVNP.CompressorRecordsOnline

variable {w : ℕ}

/-- Preservation at every call boundary, including intermediate worker calls. -/
def Stable (lo : ℕ) : Memory w → List (Report w) → Prop
  | _, [] => True
  | m, r::rs => (∀ x < lo, after m r.events x = m x) ∧ Stable lo (after m r.events) rs

namespace Stable

theorem append {lo : ℕ} {m : Memory w} {rs ts : List (Report w)} (h : Stable lo m rs)
    (ht : Stable lo (after m (eventLog rs)) ts) : Stable lo m (rs++ts) := by
  induction rs generalizing m with
  | nil => exact ht
  | cons r rs ih =>
    exact ⟨h.1,ih h.2 (by simpa only [eventLog,List.flatMap_cons,after,List.foldl_append] using ht)⟩

theorem take_eq {lo : ℕ} {m : Memory w} {rs : List (Report w)} (h : Stable lo m rs)
    (n x : ℕ) (hx : x < lo) : after m (eventLog (rs.take n)) x = m x := by
  induction rs generalizing n m with
  | nil => simp only [List.take_nil]; rfl
  | cons r rs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.take_succ_cons,eventLog,List.flatMap_cons,after,List.foldl_append]
      exact (ih h.2 n).trans (h.1 x hx)

theorem installed {g : ℕ} {base : Word w} {m : Memory w} {rs : List (Report w)}
    (stable : Stable (base.val+6) m rs) (bank : Workspace.Installed g base m) (n : ℕ) :
    Workspace.Installed g base (after m (eventLog (rs.take n))) := by
  apply bank.preserve
  intro i
  apply stable.take_eq
  rw [Fin.val_add,Fin.val_natCast]
  exact (Nat.mod_le ..).trans_lt (Nat.add_lt_add_left ((Nat.mod_le ..).trans_lt i.isLt) _)

theorem banks {g : ℕ} {base : Word w} {m : Memory w} {rs : List (Report w)}
    (stable : Stable (base.val+6) m rs) (bank : Workspace.Installed g base m) : OnlineWorkspace.Banks g base m rs := by
  induction rs generalizing m with
  | nil => trivial
  | cons r rs ih =>
    exact ⟨bank,ih stable.2 (by simpa [eventLog] using stable.installed bank 1)⟩

end Stable

variable (A : Script) (L : Layout) (base : Word w)
local notation "g" => arity A.catalog
local notation "pt" => Workspace.ports (arity A.catalog) base
local notation "H" => levelStart L 0
local notation "lo" => base.val+6

private theorem worker_stable (i : Fin A.size) (pub : Fin (A.catalog i).params → Word w)
    (bound st : Word w) (m : Memory w) (rs : List (Report w)) (fits : lo ≤ H)
    (valid : ValidTrace A.catalog i pt pub bound st m rs) (writes : Writes (H ≤ ·) (eventLog rs)) :
    Stable lo m (Online.workerRows A.catalog A.size pt i m rs) := by
  induction rs generalizing st m with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨_,_,next,ret,tail⟩ := valid
    have he := (Online.active_effect (C := A.catalog) (initial := A.initial.length) (phases := A.block.length)
      pt i m r ret).2.1
    change (∀ x < lo, after m (Online.activeReport A.catalog A.size pt i m r).events x = m x) ∧ _
    rw [he]
    refine ⟨fun x hx => after_outside m (fun a v h => writes a v (List.mem_append_left _ h)) (not_le_of_gt (hx.trans_le fits)),?_⟩
    exact ih next _ tail (fun a v h => writes a v (List.mem_append_right _ h))

/-- The three deterministic control calls retain all six physical pointers,
including in a selector row with no admitted terms. -/
theorem preparation_stable (hg : g = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w)
    (m : Memory w) (j : Fin A.size) (room : (m (pt).ordinal.val).val < directoryRows L) :
    Stable lo m (Online.preparation A.plan pt m j) := by
  have top : H = L.base+(11+g)+directoryRows L*(g+3) := by
    rw [hg]
    simp only [levelStart,levelsBase,directoryBase,plannerTag,frameBase,Nat.zero_mul,Nat.add_zero]
    omega
  have fitDir : base.val+(11+g) < 2^w := by omega
  obtain ⟨tagAddr,ordAddr,_,dirAddr,frameAddr⟩ := field_addresses g base fitDir
  let pre := Online.calendarMemory (d := A.size) pt m j
  let state := LevelCalendar.header (Online.calendar A.plan) (pt).data m
  let R := (A.phase j).recipe
  have preOrd : pre (pt).ordinal.val = m (pt).ordinal.val := ite_eq_right (by omega)
  have offset : (pt).directory.val+(pre (pt).ordinal.val).val*(g+3) < H := by
    rw [preOrd,top,dirAddr,hb]
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right room (by omega)) _
  have rowVal := Directory.rowBase_val A.catalog pt pre (offset.trans fit)
  have bound := OnlineFootprint.row_bound A L base hg hb fit pre (preOrd ▸ room)
  have lower (x : ℕ) (hx : x < lo) : x < (Controller.rowBase g (pt).data pre).val := by
    change x < (Directory.rowBase A.catalog pt pre).val
    rw [rowVal,dirAddr]
    omega
  have hc := (Online.calendar_effect A.plan pt m j).2.1
  have hr := (Online.recipe_effect A.plan pt j state pre).2.1
  have hl := (Online.launch_effect (C := A.catalog) (initial := A.initial.length) (phases := A.block.length) pt (Online.rowInput A.plan pt m j)).2.1
  change Stable lo m [Online.calendarReport A.plan pt m j, Online.recipeReport A.plan pt j state pre,
    Online.launchReport A.catalog A.size pt (Online.rowInput A.plan pt m j)]
  rw [Stable,hc]
  refine ⟨fun x hx => ite_eq_right (by omega),?_⟩
  change Stable lo pre (Online.recipeReport A.plan pt j state pre :: _)
  rw [Stable,hr]
  constructor
  · intro x hx
    have preserved := RowRecipe.row_outside R (pt).data state pre
      (by rw [PhaseRecipe.recipe_address]; exact bound.trans fit.le) x
      (.inl (by rw [PhaseRecipe.recipe_address]; exact lower x hx))
    rw [RowRecipe.after_row] at preserved
    exact (ite_eq_right (by omega : x ≠ (pt).tag.val)).trans preserved
  · change Stable lo (Online.rowInput A.plan pt m j) (Online.launchReport A.catalog A.size pt _ :: _)
    rw [Stable,hl]
    constructor
    · intro x hx
      exact Controller.after_row_outside g (pt).data (Online.rowInput A.plan pt m j) x (by change x ≠ (pt).ordinal.val; omega)
        (by change x ≠ (pt).tag.val; omega)
        (fun i => by change x ≠ ((pt).activeFrame+(i.val : Word w)).val; rw [frameAddr]; omega)
    · trivial

/-- Preparation, data and closing calls all preserve the low cells. The only
source footprint premise concerns the genuine data worker's own writes. -/
theorem row_stable (hg : g = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w)
    (m : Memory w) (j : Fin A.size) (row : Directory.Row A.size w)
    (room : (m (pt).ordinal.val).val < directoryRows L)
    (input : row.input = Online.rowInput A.plan pt m j) (valid : row.Valid A.catalog pt)
    (writes : Writes (H ≤ ·) (eventLog row.reports)) :
    Stable lo m (Online.rowLog A.plan pt m j row) := by
  have ready := preparation_stable A L base hg hb fit m j room
  have hp := (Online.preparation_effect A.plan pt 0 m j).2
  have top : H = L.base+(11+g)+directoryRows L*(g+3) := by
    rw [hg]
    simp only [levelStart,levelsBase,directoryBase,plannerTag,frameBase,Nat.zero_mul,Nat.add_zero]
    omega
  have lowTag := (field_addresses g base (by omega)).1
  have hworker := worker_stable A L base row.worker _ _ _ _ _ (by omega) valid.frame writes
  have workerEnd := workerRows_after (initial := A.initial.length) (phases := A.block.length) pt row.worker _ _ _ _ _ valid.frame
  have last := (Online.stop_effect (C := A.catalog) (initial := A.initial.length) (phases := A.block.length)
    pt row.worker (row.endMemory A.catalog pt)).2.1
  rw [Online.rowLog,List.append_assoc]
  apply ready.append
  rw [hp,← input]
  apply hworker.append
  rw [workerEnd]
  change Stable lo (row.endMemory A.catalog pt) [Online.stopReport A.catalog A.size pt row.worker _]
  rw [Stable,last]
  exact ⟨fun x hx => ite_eq_right (by omega),trivial⟩

end CompressorRecords.SourceBankFrame

end VPVNP
end Computability
end OAI
