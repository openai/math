import OAI.Computability.VPVNP.CompressorRecordsDirectory
import OAI.Computability.VPVNP.CompressorRecordsScheduleCursor
import OAI.Computability.VPVNP.CompressorRecordsCursorInit

/-!
# Launching the level-zero cursor pass from an initialized directory

The first directory row is produced by the fourteen-write initializer.
The controller snapshots the row, installs the active frame, and launches
the cursor worker at row zero. The last worker call restores the controller
tag while preserving the constructed graph directory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Directory.Cursor

open BurstRAM BurstRAM.PrivateRAM
open CursorNetwork Compression
open scoped Fin.CommRing

variable {w b l a pad columns : ℕ} {S : Type} [Fintype S]

/-- The first scheduler row uses the tag for catalog worker zero. -/
def initWords (ports : Ports w) (b l a width columns : ℕ) : Fin 8 → Word w :=
  CursorRAM.ScheduleInit.inputs ports.directory (LiveStageLink.tagWord w (0 : Fin 2).succ) b l a width columns

/-- Memory after the cursor initializer writes the first directory row for the specified
radices, degree, width and incidence columns. -/
def installed (ports : Ports w) (b l a width columns : ℕ) (m : Memory w) : Memory w :=
  after m (CursorRAM.ScheduleInit.events (initWords ports b l a width columns))

/-- The row object includes the exact reports of the source worker. The
directory dispatcher derives its tag, cursor and operand bank from RAM. -/
def row (m : Memory w) (b l a width columns : ℕ) : Row 2 w where
  input := m
  worker := 0
  fuel := 1+CursorRAM.visit.length
  choices := List.replicate (CursorRAM.rowCount b l a) []
  reports := CursorRAM.scanReports (CursorRAM.publicWords w b l a width columns) 0 (CursorRAM.rowCount b l a)

/-- The address lies before the cursor initializer's directory row or at least fourteen words
past its start. -/
def OutsideRow (ports : Ports w) (addr : Word w) : Prop :=
  addr.val < ports.directory.val ∨ ports.directory.val + 14 ≤ addr.val

/-- The active controller row launches the cursor worker at zero with the exact row count and
public operands for the initial graph. -/
structure Header (ports : Ports w) (b l a width columns : ℕ) (m : Memory w) : Prop where
  controllerTag : m ports.tag.val = 0
  active : m ports.ordinal.val < m ports.rows.val
  rowTag : m (rowBase cursorRefresh ports m).val = LiveStageLink.tagWord w (0 : Fin 2).succ
  initial : start cursorRefresh ports m = 0
  exclusive : bound cursorRefresh ports m = CursorRAM.encode w (CursorRAM.rowCount b l a)
  publicWords : words cursorRefresh ports 0 m = CursorRAM.publicWords w b l a width columns

private theorem addr_val (base : Word w) (j : ℕ) (h : base.val+j < 2^w) :
    (base + (j : Word w)).val = base.val+j := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : j < 2^w), Nat.mod_eq_of_lt h]

/-- The actual initializer produces every operand used by the controller.
The only hypotheses about incoming RAM concern the three controller cells.
Their addresses lie outside the fourteen consecutive writes. -/
theorem install (ports : Ports w) (b l a width columns : ℕ) (m : Memory w)
    (state : Word w) (rowRoom : ports.directory.val+14 ≤ 2^w)
    (tagOutside : OutsideRow ports ports.tag) (ordinalOutside : OutsideRow ports ports.ordinal)
    (countOutside : OutsideRow ports ports.rows)
    (tag : m ports.tag.val = 0) (ordinal : m ports.ordinal.val = 0) (count : 0 < m ports.rows.val) :
    let pub := initWords ports b l a width columns
    let M := (PrimedStackRAM.template CursorRAM.ScheduleInit.ops 16).instantiate w pub
    execute M.program (1+CursorRAM.ScheduleInit.ops.length) (M.program.start state) m [] =
        some ⟨CursorRAM.ScheduleInit.events pub, some (state+1)⟩ ∧
      Header ports b l a width columns (installed ports b l a width columns m) := by
  let out := installed ports b l a width columns m
  obtain ⟨hn,hr,hs,hb,hp,keep,_⟩ := CursorRAM.ScheduleInit.initialize_row ports.directory
    (LiveStageLink.tagWord w (0 : Fin 2).succ) state b l a width columns m rowRoom
  have hor : out ports.ordinal.val = 0 := (keep _ ordinalOutside).trans ordinal
  have hbase : rowBase cursorRefresh ports out = ports.directory := by
    change ports.directory + out ports.ordinal.val * _ = ports.directory
    rw [hor,zero_mul,add_zero]
  refine ⟨hn, (keep _ tagOutside).trans tag, ?_, ?_, ?_, ?_, ?_⟩
  · change out ports.ordinal.val < out ports.rows.val
    rwa [hor, show out ports.rows.val = m ports.rows.val from keep _ countOutside]
  · change out (rowBase cursorRefresh ports out).val = _
    rwa [hbase]
  · change out (rowBase cursorRefresh ports out+1).val = _
    rw [hbase, show (ports.directory+1).val = ports.directory.val+1 from
      addr_val ports.directory 1 (by omega)]
    exact hs
  · change out (rowBase cursorRefresh ports out+2).val = _
    rw [hbase, show (ports.directory+2).val = ports.directory.val+2 from
      addr_val ports.directory 2 (by omega)]
    exact hb
  · funext j
    change out ((rowBase cursorRefresh ports out+2) + ((j.val+1 : ℕ) : Word w)).val = _
    have hj : j.val < 11 := j.isLt
    have haddr : (ports.directory+2) + ((j.val+1 : ℕ) : Word w) =
        ports.directory + ((3+j.val : ℕ) : Word w) := by push_cast; ring
    rw [hbase, haddr, addr_val ports.directory _ (by omega), ← Nat.add_assoc]
    exact hp j

local notation "N₀" => CursorRAM.rowCount b l a


/-- Once the controller has read the first row, the guard and parameters
come from its computed frame. Every subsequent reload sees the same values. -/
theorem valid (ports : Ports w) (hD : 1 < b+l) (hd : 2+pad = 2^a) (bits : S → ℕ)
    (m : Memory w) (h : Header ports b l a (∑ s, bits s) columns m)
    (room : columns + 6*N₀ ≤ 2^w) (frameOk : FrameFits cursorRefresh ports)
    (tag : ports.tag.val < columns ∨ columns + 6*N₀ ≤ ports.tag.val)
    (frame : ports.activeFrame.val + 12 ≤ columns ∨ columns + 6*N₀ ≤ ports.activeFrame.val)
    (frameRoom : ports.activeFrame.val + 12 ≤ 2^w) :
    (row m b l a (∑ s, bits s) columns).Valid cursorRefresh ports := by
  have hp : 0 < N₀ := by unfold CursorRAM.rowCount; positivity
  have hv : (CursorRAM.encode w N₀).val = N₀ := Nat.mod_eq_of_lt (by omega)
  have hr := ready cursorRefresh ports m 0 frameOk h.rowTag
  rw [h.publicWords, h.exclusive] at hr
  refine ⟨h.controllerTag, h.active, (by change 0 < 57; decide), ?_, ?_⟩
  · change runSegment (((cursorRefresh 0).table.instantiate w (words cursorRefresh ports 0 m)).program)
      _ (some (start cursorRefresh ports m)) _ _ = _
    rw [h.publicWords, h.initial]
    let pub := CursorRAM.publicWords w b l a (∑ s, bits s) columns
    change runSegment ((PrimedStackRAM.template CursorRAM.visit 0).instantiate w pub).program
      (1+CursorRAM.visit.length) (some 0) (prepared cursorRefresh ports m) (List.replicate N₀ []) =
        some (CursorRAM.scanReports pub 0 N₀)
    simpa only [Fin.ofNat_eq_cast, Nat.cast_zero] using
      CursorRAM.scan_native (CursorRAM.publicWords w b l a (∑ s, bits s) columns) 0 N₀ (prepared cursorRefresh ports m)
  · change ValidTrace cursorRefresh 0 ports (words cursorRefresh ports 0 m)
      (bound cursorRefresh ports m) (start cursorRefresh ports m) _ _
    rw [h.publicWords, h.exclusive, h.initial]
    have he := cursor_valid_trace ports (CursorRAM.publicWords w b l a (∑ s, bits s) columns) 0 N₀
      (prepared cursorRefresh ports m) (CursorRAM.encode w N₀) (by omega) hr
      (cursor_disjoint_layout hD hd bits ports room tag frame frameRoom)
    simpa only [row, Row.dataMemory, Fin.ofNat_eq_cast, Nat.cast_zero] using he

/-- A level-zero row, including its controller launch, has the source
cursor pass's six writes per slot and a fixed dispatcher overhead. -/
theorem row_effect (ports : Ports w) (m : Memory w) (b l a width columns : ℕ)
    (initial : start cursorRefresh ports m = 0) :
    let R := row m b l a width columns
    after m (eventLog (R.log cursorRefresh ports)) = R.post cursorRefresh ports ∧
      endState (some 0) (R.log cursorRefresh ports) = some 0 ∧
      RAMBuckets.cost Report.probes (R.log cursorRefresh ports) = 20*CursorRAM.rowCount b l a + 47 := by
  let pub := CursorRAM.publicWords w b l a width columns
  let n := CursorRAM.rowCount b l a
  let pre := prepared cursorRefresh ports m
  let rs := cursorPassReports ports pub 0 n pre
  let head := launchReport cursorRefresh ports m
  have he := launch_effect cursorRefresh ports m
  have ht := cursor_pass_effect ports pub 0 n pre
  change after m (eventLog (head :: rs)) = _ ∧ endState (some 0) (head :: rs) = _ ∧
    RAMBuckets.cost Report.probes (head :: rs) = _
  refine ⟨?_, ?_, ?_⟩
  · simp only [eventLog, List.flatMap_cons, after, List.foldl_append]
    change after (after m head.events) (eventLog rs) = _
    rw [he.2.1]
    exact ht.1
  · change endState head.result rs = some 0
    rw [he.1, initial]
    exact ht.2.1
  · rw [RAMBuckets.cost, he.2.2.1, ht.2.2.2]
    have harity : arity cursorRefresh = 11 := by decide
    rw [harity]
    omega

/-- Execute the native row producer, launch the controller from the resulting
RAM, run the full incidence scan, and splice any following rows at the exact
post-state. The resulting external memory represents the typed cursor graph. -/
theorem initialize_and_launch (ports : Ports w) (hD : 1 < b+l) (hd : 2+pad = 2^a)
    (bits : S → ℕ) (m : Memory w) (state : Word w)
    (rowRoom : ports.directory.val+14 ≤ 2^w)
    (tagOutside : OutsideRow ports ports.tag) (ordinalOutside : OutsideRow ports ports.ordinal)
    (countOutside : OutsideRow ports ports.rows)
    (tagZero : m ports.tag.val = 0) (ordinal : m ports.ordinal.val = 0) (count : 0 < m ports.rows.val)
    (room : columns + 6*N₀ ≤ 2^w) (widthFits : (∑ s, bits s) < 2^w)
    (frameOk : FrameFits cursorRefresh ports)
    (tag : ports.tag.val < columns ∨ columns + 6*N₀ ≤ ports.tag.val)
    (frame : ports.activeFrame.val + 12 ≤ columns ∨ columns + 6*N₀ ≤ ports.activeFrame.val)
    (frameRoom : ports.activeFrame.val + 12 ≤ 2^w) {cap : ℕ} (hcap : 119 ≤ cap)
    (tail : List (List Bool)) :
    let init := initWords ports b l a (∑ s, bits s) columns
    let M := (PrimedStackRAM.template CursorRAM.ScheduleInit.ops 16).instantiate w init
    let input := installed ports b l a (∑ s, bits s) columns m
    let R := row input b l a (∑ s, bits s) columns
    let D := program cursorRefresh ports
    let mem := R.post cursorRefresh ports
    let rs := R.log cursorRefresh ports
    let X := cursorState (cursorCoordinateLabels b l) hD hd bits
    execute M.program (1+CursorRAM.ScheduleInit.ops.length) (M.program.start state) m [] =
        some ⟨CursorRAM.ScheduleInit.events init, some (state+1)⟩ ∧
      R.Valid cursorRefresh ports ∧
      runSegment D cap (some 0) input (R.choicesWithControl ++ tail) =
        (runSegment D cap (some 0) mem tail).map (rs ++ ·) ∧
      after input (eventLog rs) = mem ∧ endState (some 0) rs = some 0 ∧
      mem ports.tag.val = 0 ∧ (CursorRAM.directory w b l a columns).Represents X mem ∧
      RAMBuckets.cost Report.probes rs = 20*N₀+47 := by
  let input := installed ports b l a (∑ s, bits s) columns m
  let R := row input b l a (∑ s, bits s) columns
  obtain ⟨hi, hh⟩ := install ports b l a (∑ s, bits s) columns m state rowRoom tagOutside ordinalOutside
    countOutside tagZero ordinal count
  have hv := valid ports hD hd bits input hh room frameOk tag frame frameRoom
  obtain ⟨hm,hr,hc⟩ := row_effect ports input b l a (∑ s, bits s) columns hh.initial
  have hbound : Row.capNeeded cursorRefresh R = 119 := by
    unfold Row.capNeeded
    rw [show arity cursorRefresh = 11 by decide]
    rfl
  have hs := Row.segment cursorRefresh ports R hv (by omega) (hbound ▸ hcap) tail
  refine ⟨hi, hv, hs, hm, hr, ?_, ?_, hc⟩
  · simp [Row.post, writeMemory]
  · apply cursor_directory_write_tag hD hd bits room ports.tag 0 tag
    exact (CursorRAM.initialize_cursor hD hd bits room widthFits (prepared cursorRefresh ports input)).2.1

end CompressorRecords.Schedule.Directory.Cursor

end VPVNP
end Computability
end OAI
