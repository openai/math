import OAI.Computability.VPVNP.CompressorRecordsSchedule
import OAI.Computability.VPVNP.CompressorRecordsController

/-!
# Native execution of a level-major descriptor directory

Every row supplies a worker tag, a starting cursor, an exclusive stop, and
a fixed-pitch parameter bank. The dispatcher executes the controller, then
the chosen worker for all its data calls, and then returns to the controller.
The row theorem composes an actual verified source run with any remaining
directory. Its cost is linear in the source calls plus probes and the row
count, with constants fixed by the catalog.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Directory

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {d w : ℕ} (C : Catalog d) (ports : Ports w)

/-- A fixed number of pass slots per level. An optional initial segment,
such as the level-zero cursor construction, precedes the repeated levels. -/
def levelOrdinal {slots : ℕ} (first level : ℕ) (slot : Fin slots) : ℕ :=
  first + level*slots + slot.val

/-- Natural address of a field in the fixed-pitch directory, indexed by row ordinal and field
offset. -/
def address (base arity ordinal : ℕ) (field : Fin (arity + 3)) : ℕ :=
  base + ordinal*(arity+3) + field.val

theorem address_injective (base arity : ℕ) :
    Function.Injective (fun p : ℕ × Fin (arity+3) ↦ address base arity p.1 p.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change base + i*(arity+3) + a.val = base + j*(arity+3) + b.val at h
  have he : i*(arity+3)+a.val = j*(arity+3)+b.val := by omega
  have ha := congrArg (· % (arity+3)) he
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at ha
  obtain rfl : a = b := Fin.ext ha
  have hx := Nat.add_right_cancel he
  exact Prod.ext (Nat.eq_of_mul_eq_mul_right (by omega) hx) rfl

/-- A descriptor program with one finite table independent of the number
of repetitions, directory rows, address width, and live input length. -/
abbrev table := Schedule.template C (Controller.table (arity C))

/-- The native program that dispatches between the fixed-arity directory controller and the
catalog's data workers. -/
abbrev program := (Schedule.machine C (Controller.table (arity C)) ports).program

/-- The current directory row's word address, computed from the published directory base, row
ordinal and catalog arity. -/
def rowBase (m : Memory w) := Controller.rowBase (arity C) ports.data m

theorem rowBase_val (m : Memory w)
    (fit : ports.directory.val + (m ports.ordinal.val).val * (arity C + 3) < 2 ^ w) :
    (rowBase C ports m).val = ports.directory.val + (m ports.ordinal.val).val*(arity C+3) := by
  exact Controller.rowBase_val (arity C) ports.data m fit

/-- The linked controller report that snapshots the active row and starts its selected worker
at the stored cursor. -/
def launchReport (m : Memory w) :=
  LiveStageLink.linkedReport handoff ports.tag (0 : Fin (d+1)) (Controller.rowReport
    (arity C) ports.data m)

/-- The linked accepting controller report emitted when the directory ordinal has reached the
total row count. -/
def terminalReport (m : Memory w) :=
  LiveStageLink.linkedReport (handoff (d := d)) ports.tag 0 (Controller.doneReport ports.data m)

/-- Memory after the controller launches an active row, with its worker operands and stop bound
installed in the active frame. -/
def prepared (m : Memory w) := after m (Controller.rowReport (arity C) ports.data m).events

/-- The worker's initial cursor, read from offset one of the current directory row. -/
def start (m : Memory w) := m (rowBase C ports m + 1).val
/-- The worker's exclusive stopping cursor, read from offset two of the current directory row. -/
def bound (m : Memory w) := m (rowBase C ports m + 2).val
/-- The public parameter words of the selected worker, read in order immediately after the
row's stop bound. -/
def words (i : Fin d) (m : Memory w) : Fin (C i).params → Word w :=
  fun j ↦ Controller.field (rowBase C ports m + 2) m (j.val+1)

/-- Internal controller memory effects and the precise next cursor. -/
theorem launch_effect (m : Memory w) :
    (launchReport C ports m).result = some (start C ports m) ∧
      after m (launchReport C ports m).events = prepared C ports m ∧
      (launchReport C ports m).probes = 7+2*(arity C+1) ∧
      choiceBits (launchReport C ports m).events = [] := by
  let q := Controller.rowReport (arity C) ports.data m
  have hn : handoff (0 : Fin (d+1)) = none := rfl
  have hq : q.result = some (start C ports m) := rfl
  have hc := Controller.rowReport_cost (arity C) ports.data m
  refine ⟨?_,?_,?_,?_⟩
  · change (LiveStageLink.linkedReport handoff ports.tag 0 q).result = _
    simp [LiveStageLink.linkedReport, LiveStageLink.prependLog, LiveStageLink.exitReport, hq]
  · rw [launchReport, LiveStageLink.linkedReport_after, hn]
    rfl
  · rw [launchReport, LiveStageLink.linkedReport_probes, hn]
    change q.probes + 1 + (if q.result = none ∧ _ then 1 else 0) = _
    have hp : q.probes = 6+2*(arity C+1) := hc.2.1
    simp [hp,hq]
    omega
  · rw [launchReport, LiveStageLink.linkedReport_choiceBits]
    exact hc.2.2

theorem terminal_effect (m : Memory w) :
    (terminalReport (d := d) ports m).result = none ∧ after m (terminalReport (d :=
      d) ports m).events = m ∧
      (terminalReport (d := d) ports m).probes = 3 ∧ choiceBits (terminalReport (d :=
        d) ports m).events = [] := by
  have hn : handoff (0 : Fin (d+1)) = none := rfl
  refine ⟨?_,?_,?_,?_⟩
  · rfl
  · rw [terminalReport, LiveStageLink.linkedReport_after, hn]; rfl
  · rw [terminalReport, LiveStageLink.linkedReport_probes, hn]; rfl
  · rw [terminalReport, LiveStageLink.linkedReport_choiceBits]; rfl

theorem launch (m : Memory w) (st : Word w) (htag : m ports.tag.val = 0) (fits : d + 1 ≤ 2 ^ w)
    (active : m ports.ordinal.val < m ports.rows.val) {cap : ℕ}
    (hcap : 20 + 6 * (arity C + 1) + 2 * (d + 1) + 5 ≤ cap) :
    execute (program C ports) cap ((program C ports).start st) m [] = some
      (launchReport C ports m) := by
  apply controller_call C (Controller.table (arity C)) ports st m [] htag fits hcap
  exact Controller.execute_row (arity C) ports.data st m [] _ active le_rfl

theorem terminate (m : Memory w) (st : Word w) (htag : m ports.tag.val = 0) (fits : d + 1 ≤ 2 ^ w)
    (closed : m ports.rows.val ≤ m ports.ordinal.val) {cap : ℕ} (hcap : 6 + 2 *
      (d + 1) + 5 ≤ cap) :
    execute (program C ports) cap ((program C ports).start st) m [] = some (terminalReport (d :=
      d) ports m) := by
  apply controller_call C (Controller.table (arity C)) ports st m [] htag fits hcap
  exact Controller.execute_done (arity C) ports.data st m [] _ closed le_rfl

/-- Separation of the active parameter bank from the two mutable control
cells. The controller snapshots the full source row before writing the bank. -/
def FrameFits : Prop :=
  arity C+1 ≤ 2^w ∧ ∀ j : Fin (arity C+1),
    ports.activeFrame + (j.val : Word w) ≠ ports.ordinal ∧ ports.activeFrame + (j.val : Word w)
      ≠ ports.tag

theorem ready (m : Memory w) (i : Fin d) (fits : FrameFits C ports)
    (rowTag : m (rowBase C ports m).val = LiveStageLink.tagWord w i.succ) :
    Ready C i ports (words C ports i m) (bound C ports m) (prepared C ports m) := by
  have h (j : Fin (arity C+1)) : prepared C ports m (ports.activeFrame+(j.val : Word w)).val =
      Controller.field (rowBase C ports m+2) m j.val :=
    Controller.after_row_frame (arity C) ports.data m j fits.1 (fits.2 j).1 (fits.2 j).2
  refine ⟨(Controller.after_row_tag (arity C) ports.data m).trans rowTag, ?_, ?_⟩
  · simpa [stopWord, bound, Controller.field] using h 0
  · funext j
    exact h ⟨j.val+1, Nat.succ_lt_succ (j.isLt.trans_le (params_le_arity C i))⟩

/-- One scheduled worker invocation. Its operand words, starting state,
and bound are read from its row in the entry memory. -/
structure Row (d w : ℕ) where
  /-- Entry memory in which the directory controller finds the row and reads its operands. -/
  input : Memory w
  /-- Catalog index of the worker selected for this row. -/
  worker : Fin d
  /-- Instruction fuel supplied to each call of the row's source worker. -/
  fuel : ℕ
  /-- The ordered choice-bit streams supplied to the source worker's data calls. -/
  choices : List (List Bool)
  /-- The source worker reports for the row's data calls, in execution order. -/
  reports : List (Report w)

namespace Row

/-- Surround the worker choice streams with empty streams for the controller launch and closing
call. -/
def choicesWithControl (row : Row d w) : List (List Bool) := [] :: (row.choices ++ [[]])

/-- Memory passed to the first worker data call after the controller has installed this row's
active frame. -/
def dataMemory (row : Row d w) := prepared C ports row.input

/-- Memory after replaying all source worker reports from the prepared data memory. -/
def endMemory (row : Row d w) := after (row.dataMemory C ports) (eventLog row.reports)

/-- Memory after the row finishes and restores the controller stage tag to zero. -/
def post (row : Row d w) := writeMemory (row.endMemory C ports) ports.tag 0

/-- The complete linked report list for a directory row, from the controller launch through all
data calls and the closing handoff. -/
def log (row : Row d w) : List (Report w) :=
  launchReport C ports row.input ::
    (linkedRows C row.worker ports (row.dataMemory C ports) row.reports ++
      [closedLinkedReport C row.worker ports (row.endMemory C ports)])

/-- The active row starts under the controller tag, has positive fuel, and its source reports
form an actual run respecting the loaded frame and cursor bound. -/
structure Valid (row : Row d w) : Prop where
  controllerTag : row.input ports.tag.val = 0
  active : row.input ports.ordinal.val < row.input ports.rows.val
  positiveFuel : 0 < row.fuel
  sourceRun : runSegment ((C row.worker).table.instantiate w
    (words C ports row.worker row.input)).program
    row.fuel (some (start C ports row.input)) (row.dataMemory C ports) row.choices =
      some row.reports
  frame : ValidTrace C row.worker ports (words C ports row.worker row.input)
    (bound C ports row.input)
    (start C ports row.input) (row.dataMemory C ports) row.reports

/-- A per-call fuel bound covering the controller, the row's source worker and active-frame
loads, and the outer stage dispatch. -/
def capNeeded (row : Row d w) :=
  max (20+6*(arity C+1)) (row.fuel+3+4*((C row.worker).params+1)) + 2*(d+1)+5

/-- From controller entry through the full original pass and its handoff.
The tail can itself start another pass with newly computed parameters. -/
theorem segment (row : Row d w) (v : row.Valid C ports) (fits : d + 1 ≤ 2 ^ w) {cap : ℕ}
    (hc : capNeeded C row ≤ cap) (tail : List (List Bool)) :
    runSegment (program C ports) cap (some 0) row.input (row.choicesWithControl ++ tail) =
      (runSegment (program C ports) cap (some 0) (row.post C ports) tail).map (row.log C ports
        ++ ·) := by
  unfold capNeeded at hc
  have hr := launch C ports row.input 0 v.controllerTag fits v.active (cap := cap) (by omega)
  have h := launch_effect C ports row.input
  simp only [choicesWithControl, List.cons_append, List.append_assoc, List.nil_append, runSegment,
    hr, h.1, h.2.1]
  change (runSegment (Schedule.machine C (Controller.table (arity C)) ports).program cap
    (some (start C ports row.input)) (row.dataMemory C ports) (row.choices ++ [] :: tail)).map _ = _
  rw [worker_segment C (Controller.table (arity C)) row.worker ports _ _ _ _ _ _ row.fuel cap
    v.positiveFuel fits
    (by omega) v.sourceRun v.frame tail]
  simp only [log, post, endMemory, dataMemory, Option.map_map, Function.comp_def,
    List.cons_append, List.append_assoc,
    List.nil_append]

/-- Exact source and scheduler charges through one full row, including the
controller launch, active data calls, and the empty-choice closing call. -/
theorem cost (row : Row d w) (v : row.Valid C ports) :
    RAMBuckets.cost Report.probes (row.log C ports) =
      RAMBuckets.cost Report.probes row.reports + row.reports.length*((C row.worker).params+2) +
        ((C row.worker).params+4) + (8+2*(arity C+1)) := by
  rw [log, endMemory, RAMBuckets.cost, (launch_effect C ports row.input).2.2.1,
    linkedPass_cost C row.worker ports
    (words C ports row.worker row.input) (bound C ports row.input) (start C ports row.input)
      _ _ v.frame]
  omega

end Row

/-- Memory at the terminal controller, after the last worker handoff. -/
def finalMemory (m : Memory w) : List (Row d w) → Memory w
  | [] => m
  | row :: rest => finalMemory (row.post C ports) rest

/-- Compatibility at every native row boundary, with directory exhaustion
checked at the terminal controller. A worker may write later rows. -/
def Valid (cap : ℕ) (m : Memory w) : List (Row d w) → Prop
  | [] => m ports.tag.val = 0 ∧ m ports.rows.val ≤ m ports.ordinal.val
  | row :: rest => row.input = m ∧ row.Valid C ports ∧ row.capNeeded C ≤ cap ∧ Valid cap
    (row.post C ports) rest

/-- The native full directory run accepts these exact streams and computes
the indicated reports for all the selected rows. -/
theorem run (rows : List (Row d w)) (m : Memory w) (cap : ℕ) (fits : d + 1 ≤ 2 ^ w)
    (hcap : 6 + 2 * (d + 1) + 5 ≤ cap) (v : Valid C ports cap m rows) :
    runSegment (program C ports) cap (some 0) m (rows.flatMap Row.choicesWithControl ++ [[]]) =
      some (rows.flatMap (Row.log C ports) ++ [terminalReport (d := d) ports
        (finalMemory C ports m rows)]) := by
  induction rows generalizing m with
  | nil =>
    obtain ⟨htag,closed⟩ := v
    rw [List.flatMap_nil, List.nil_append, runSegment, terminate C ports m 0 htag fits closed hcap]
    rfl
  | cons row rest ih =>
    obtain ⟨rfl, hrow, hrowCap, hrest⟩ := v
    rw [List.flatMap_cons, List.append_assoc, row.segment C ports hrow fits hrowCap, ih _ hrest]
    simp [finalMemory]

/-- The total linked charge depends only on native source charges and
the row count. The constants depend on the fixed worker catalog. -/
theorem cost_bound (rows : List (Row d w)) (m : Memory w) (cap : ℕ) (v : Valid C ports cap m rows) :
    RAMBuckets.cost Report.probes
      (rows.flatMap (Row.log C ports) ++ [terminalReport (d := d) ports
        (finalMemory C ports m rows)]) ≤
      (rows.map fun row ↦ RAMBuckets.cost Report.probes row.reports).sum * (arity C+3) +
        rows.length*(3*arity C+14) + 4 := by
  induction rows generalizing m with
  | nil =>
    simp only [List.flatMap_nil, List.nil_append, finalMemory, List.map_nil, List.sum_nil,
      List.length_nil, Nat.zero_mul, Nat.zero_add, RAMBuckets.cost, (terminal_effect (d :=
        d) ports m).2.2.1]
    decide
  | cons row rest ih =>
    obtain ⟨rfl,hrow,_,hrest⟩ := v
    have prev := ih _ hrest
    have len : row.reports.length ≤ RAMBuckets.cost Report.probes row.reports := by
      rw [RAMBuckets.cost_eq_length_add_probes]; omega
    have hk := params_le_arity C row.worker
    have hm := Nat.mul_le_mul len (Nat.add_le_add_right hk 2)
    rw [List.flatMap_cons, finalMemory, List.append_assoc, RAMBuckets.cost_append,
      row.cost C ports hrow,
      List.map_cons, List.sum_cons, Nat.add_mul, List.length_cons, Nat.add_mul, Nat.one_mul]
    have hmul : RAMBuckets.cost Report.probes row.reports * (arity C+3) =
        RAMBuckets.cost Report.probes row.reports * (arity C+2) + RAMBuckets.cost Report.probes
          row.reports := by
      rw [show arity C+3 = (arity C+2)+1 by omega, Nat.mul_succ]
    omega

end CompressorRecords.Schedule.Directory

end VPVNP
end Computability
end OAI
