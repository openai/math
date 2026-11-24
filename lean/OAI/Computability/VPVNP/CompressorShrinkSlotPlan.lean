import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner
import OAI.Computability.VPVNP.CompressorRecordsLevelFields
import OAI.Computability.VPVNP.CompressorSlotOutputRecipe
import OAI.Computability.VPVNP.CompressorSlotIncidence
import OAI.Computability.VPVNP.CompressorSlotWidthScan
import OAI.Computability.VPVNP.CompressorSlotOwnerAux
import OAI.Computability.VPVNP.CompressorSlicePreparation

/-!
# The chronological shrinking slot program

Four fixed writes install the subdivision counts. Two scans prepare the
selected role and cyclic successor tables, and one clears the append counters.
Five sorted-slot scans and four output scans fill the six incidence columns.
Finally the program copies these columns, at their own base or lane-slot
lengths, into the following level's canonical incidence arrays.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotPlan

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PhaseRecipe BlockPlanner
open scoped Fin.CommRing

/-- Fixed tag, degree, color and subdivision data used to build the shrinking output slots. -/
abbrev Template := SlotLevel.Recipe.Template
/-- Runtime expressions for the graph dimensions and table heads needed by the shrinking slot
recipes. -/
abbrev Inputs := SlotLevel.Recipe.Inputs

private def coreOps : (p : SlotLevel.Phase) → Expr → (Fin (SlotLevel.arity p) → Expr) → Visit
  | .genuineOwners => ops SlotOwners.genuine 0 (.lit 0)
  | .dummyOwners => ops SlotOwners.dummy 0 (.lit 0)
  | .appendFields => ops collectPreimage 3 (.lit 0)
  | .invertFields => ops SlotScatter.visit 0 (.lit 0)
  | .baseMatching => ops SlotBaseScan.code 0 (.lit 0)

private def outputOps : (p : ShrinkSlots.Recipe.Phase) → Expr → (Fin (ShrinkSlots.Recipe.arity p) → Expr) → Visit
  | .baseInverse => ops SlotScatter.visit 0 (.lit 0)
  | .actualOut => ops (SlotIncidencePass.visit false) 0 (.lit 0)
  | .actualIn => ops (SlotIncidencePass.visit true) 0 (.lit 0)
  | .widths => ops SlotWidthScan.visit 0 (.lit 0)

/-- Build the visit for a slot-core phase using its phase-specific stop bound and public
operand expressions. -/
def core (T : Template) (I : Inputs) (p : SlotLevel.Phase) : Visit :=
  coreOps p (SlotLevel.Recipe.stop T I p) (SlotLevel.Recipe.params T I p)

/-- Build the visit for an output incidence phase, supplying the split-width head along with
its derived operands. -/
def output (T : Template) (I : Inputs) (split : Expr) (p : ShrinkSlots.Recipe.Phase) : Visit :=
  outputOps p (ShrinkSlots.Recipe.stop T I p) (ShrinkSlots.Recipe.params T I split p)

/-- Publish one role's fixed subdivision count in the runtime subdivision table. -/
def subdivision (T : Template) (I : Inputs) (i : Fin 4) : Visit :=
  publish (I.subdivisions.add (.lit i.val)) (.lit (T.subdivisions i))

/-- The eight-row pass that publishes the role lookup for the selected layout side. -/
def roles (I : Inputs) (layout : Expr) : Visit :=
  ops SlotOwners.Aux.roleCode 0 (.lit 0) (.lit 8) ![layout,I.role]

/-- The pass that fills the cyclic successor-site table from the lane and tag counts. -/
def cyclic (T : Template) (I : Inputs) : Visit :=
  ops SlotOwners.Aux.nextCode 0 (.lit 0) (SlotLevel.Recipe.counts T I).sites ![I.lanes,.lit T.tags,I.nextSite]

/-- The unused owners have append counters too. Clear their cells and the real
owners' cells before the uninterrupted five scans. -/
def clear (T : Template) (I : Inputs) : Visit :=
  let c := SlotLevel.Recipe.counts T I
  ops SliceRAM.clearOps 0 (.lit 0) (c.owners.add c.fields) (fun _ ↦ I.scratch.add c.fields)

/-- Expressions for the six constructed incidence-column heads used as sources of the final
copy passes. -/
def sourceHeads (T : Template) (I : Inputs) := ShrinkSlots.Recipe.columnHeads T I

/-- The number of cells to copy for a column, using the base-arc count for the first three
columns and the actual port count for the last three. -/
def columnCount (T : Template) (I : Inputs) (c : Fin 6) :=
  if c.val < 3 then (SlotLevel.Recipe.counts T I).baseArcs else (ShrinkSlots.Recipe.columns T I).count

/-- Copy a completed incidence column from the shrinking slot arena to the canonical head
published by the next level. -/
def copyColumn (T : Template) (I : Inputs) (shape : DescriptorSpace.Shape) (step : ℕ) (c : Fin 6) : Visit :=
  copy (columnCount T I c) (sourceHeads T I c) (LevelFields.incidence shape (step+1) c)

/-- The list itself fixes the order of the native workers. Expression evaluation
supplies the current heads, selected layout and split-width input at runtime. -/
def visits (T : Template) (I : Inputs) (layout split : Expr) (shape : DescriptorSpace.Shape) (step : ℕ) :
    List Visit :=
  List.ofFn (subdivision T I) ++ [roles I layout, cyclic T I, clear T I,
    core T I .genuineOwners, core T I .dummyOwners, core T I .appendFields, core T I .invertFields,
    core T I .baseMatching, output T I split .baseInverse, output T I split .actualOut,
    output T I split .actualIn, output T I split .widths] ++ List.ofFn (copyColumn T I shape step)

@[simp] theorem visits_length (T : Template) (I : Inputs) (layout split : Expr) (shape : DescriptorSpace.Shape)
    (step : ℕ) : (visits T I layout split shape step).length = 22 := by simp [visits]

/-- Public-bank widths, in chronological order. The rectangular catalog can
reserve eight parameter words for every shrinking slot visit. -/
theorem operand_counts (T : Template) (I : Inputs) (layout split : Expr) (shape : DescriptorSpace.Shape)
    (step : ℕ) :
    ((visits T I layout split shape step).map fun v ↦ v.worker.params) =
      [2,2,2,2,2,3,1,8,3,6,2,6,2,5,5,8,3,3,3,3,3,3] := rfl

variable {w : ℕ} {pub : Fin 5 → Word w} {state : Word w} {m : Memory w}
variable {bases lanes : ℕ} {h : SlotLevel.Heads} (T : Template) (I : Inputs)
variable (read : SlotLevel.Recipe.Reads I pub state m bases lanes h)

/-- Agreement of a worker's actual register arity, cursor bounds and operands
with its native unpadded frame. The external catalog assigns its tag. -/
def words (v : Visit) (tag : Word w) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) : List (Word w) :=
  tag :: v.initial.eval pub state m :: v.stop.eval pub state m ::
    List.ofFn (fun i ↦ (v.params i).eval pub state m)

/-- The chronological script compiler uses the worker's position as its tag
and pads the checked operand list to the largest arity in the catalog. -/
theorem script_words (A : BlockPlanner.Script) (j : Fin A.size) :
    (A.phase j).recipe.words pub state m =
      words (A.visit j) (j.succ.val : Word w) pub state m ++
      List.replicate (Schedule.arity A.catalog-(A.visit j).worker.params) 0 := by
  let v := A.visit j
  let phase : PhaseRecipe.Phase v.worker.params := ⟨j.succ.val,v.initial,v.stop,v.params⟩
  have hp := SlotLevel.Recipe.pad_phase_words (Schedule.params_le_arity A.catalog j) phase pub state m
  exact hp.trans (congrArg (fun xs ↦ xs ++ List.replicate _ 0) (PhaseRecipe.recipe_words phase pub state m))

include read in
theorem core_words (p : SlotLevel.Phase) (tag : Word w) :
    words (core T I p) tag pub state m = SlotLevel.frame (T.shape bases lanes) h (fun _ ↦ tag) p := by
  have hs := SlotLevel.Recipe.eval_stop T I p read
  have hp := funext (SlotLevel.Recipe.eval_params T I p read)
  cases p <;> exact congrArg₂ (fun u v ↦ tag :: 0 :: u :: List.ofFn v) hs hp

include read in
theorem output_words (split : Expr) {splitHead : ℕ} (hsplit : split.eval pub state m = (splitHead : Word w))
    (p : ShrinkSlots.Recipe.Phase) (tag : Word w) :
    words (output T I split p) tag pub state m = ShrinkSlots.Recipe.frame (T.shape bases lanes) h splitHead
      (fun _ ↦ tag) p := by
  have hs := ShrinkSlots.Recipe.eval_stop T I read p
  have hp := funext (ShrinkSlots.Recipe.eval_params T I split read p hsplit)
  cases p <;> exact congrArg₂ (fun u v ↦ tag :: 0 :: u :: List.ofFn v) hs hp

include read in
theorem subdivision_words (tag : Word w) (i : Fin 4) :
    words (subdivision T I i) tag pub state m =
      [tag,0,1,((h.subdivisions+i.val : ℕ) : Word w),(T.subdivisions i : Word w)] := by
  change [tag,0,1,I.subdivisions.eval pub state m+(i.val : Word w),(T.subdivisions i : Word w)] = _
  rw [read.subdivisions_eq,Nat.cast_add]

include read in
theorem cyclic_words (tag : Word w) :
    words (cyclic T I) tag pub state m =
      [tag,0,(SlotLevel.sites (T.shape bases lanes) : Word w),(lanes : Word w),(T.tags : Word w),(h.nextSite : Word w)] := by
  have hc := SlotLevel.Recipe.eval_counts T I read
  change tag :: 0 :: (SlotLevel.Recipe.counts T I).sites.eval pub state m :: I.lanes.eval pub state m :: (T.tags : Word w) :: I.nextSite.eval pub state m :: [] = _
  rw [read.lanes_eq,read.nextSite_eq,show (SlotLevel.Recipe.counts T I).sites.eval pub state m =
    (SlotLevel.sites (T.shape bases lanes) : Word w) from congrArg SlotLevel.Recipe.Counts.sites hc]

include read in
theorem role_words (layout : Expr) (chosen : Bool) (hl : layout.eval pub state m = (chosen.toNat : Word w))
    (tag : Word w) :
    words (roles I layout) tag pub state m = [tag,0,8,(chosen.toNat : Word w),(h.role : Word w)] := by
  change [tag,0,8,layout.eval pub state m,I.role.eval pub state m] = _
  rw [hl,read.role_eq]

include read in
theorem clear_words (tag : Word w) :
    let s := T.shape bases lanes
    words (clear T I) tag pub state m =
      [tag,0,((SlotLevel.owners s + SlotLevel.fields s : ℕ) : Word w), ((h.scratch+SlotLevel.fields s : ℕ) : Word w)] := by
  intro s
  let c := SlotLevel.Recipe.counts T I
  have hc := SlotLevel.Recipe.eval_counts T I read
  have ho : c.owners.eval pub state m = (SlotLevel.owners s : Word w) := congrArg SlotLevel.Recipe.Counts.owners hc
  have hf : c.fields.eval pub state m = (SlotLevel.fields s : Word w) := congrArg SlotLevel.Recipe.Counts.fields hc
  change [tag,0,c.owners.eval pub state m + c.fields.eval pub state m,I.scratch.eval pub state m + c.fields.eval pub state m] = _
  rw [ho,hf,read.scratch_eq,Nat.cast_add,Nat.cast_add]

/-- Even with arbitrary old scratch contents, the clearing worker establishes
the zero-counter input to the five native scans and preserves every earlier input table. -/
theorem clear_run (s : SlotLevel.Shape) (h : SlotLevel.Heads) (mem : Memory w)
    (fit : SlotLevel.rowsHead s h < 2^w) :
    let start := h.scratch + SlotLevel.fields s
    let n := SlotLevel.owners s + SlotLevel.fields s
    let P := ((template SliceRAM.clearOps 0).instantiate w (fun _ ↦ (start : Word w))).program
    ∃ rs, runSegment P 8 (some 0) mem (List.replicate n []) = some rs ∧
      (∀ u : Word w, u.val < n → after mem (eventLog rs) (start+u.val) = 0) ∧
      (∀ a, a < start ∨ SlotLevel.rowsHead s h ≤ a → after mem (eventLog rs) a = mem a) ∧
      endState (some 0) rs = some (Fin.ofNat _ n) ∧ rs.length = n ∧
      ∀ r ∈ rs, r.probes = 1 ∧ r.events.length+1 = 8 := by
  intro start n P
  have room : start+n < 2^w := fit
  have val : (start : Word w).val = start := Nat.mod_eq_of_lt (by omega)
  obtain ⟨rs,run,zero,frame,cursor,length,work⟩ :=
    SliceRAM.clearPass_run (start : Word w) n (by rw [val]; omega) (by omega) mem
  rw [val] at zero frame
  exact ⟨rs,run,fun u hu ↦ zero _ (by omega) (by omega),fun a ha ↦ frame a ha,cursor,length,work⟩

include read in
theorem copy_words (tag : Word w) (shape : DescriptorSpace.Shape) (step : ℕ) (c : Fin 6) :
    let s := T.shape bases lanes
    let n := if c.val < 3 then SlotLevel.baseArcs s else ShrinkSlots.actualCount s
    words (copyColumn T I shape step c) tag pub state m =
      [tag,0,(n : Word w),0,(ShrinkSlots.directory s h w).column c,(LevelFields.incidence shape (step+1) c).eval pub state m] := by
  intro s n
  have hc := SlotLevel.Recipe.eval_counts T I read
  have count : (columnCount T I c).eval pub state m = (n : Word w) := by
    by_cases hbase : c.val < 3
    · simp only [columnCount,n,hbase,↓reduceIte]
      exact congrArg SlotLevel.Recipe.Counts.baseArcs hc
    · simp only [columnCount,n,hbase,↓reduceIte]
      exact (ShrinkSlots.Recipe.eval_columns T I read).count
  change [tag,0,(columnCount T I c).eval pub state m,0,(sourceHeads T I c).eval pub state m,
    (LevelFields.incidence shape (step+1) c).eval pub state m] = _
  rw [count,show (sourceHeads T I c).eval pub state m = _ from ShrinkSlots.Recipe.eval_columnHeads T I read c]

end CompressorRecords.ShrinkSlotPlan

end VPVNP
end Computability
end OAI
