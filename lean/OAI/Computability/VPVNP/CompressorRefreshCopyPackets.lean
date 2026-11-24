import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorShrinkSlotFootprint
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorSourceScanned

/-!
# The six successor - incidence copy launches in the refresh script

Each column resets its own cursor and reads its source and destination pointers
from the persisted physical headers. The fixed packet window copies the three
base - port columns and the three actual - port columns at their respective lengths.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshCopyPackets

open BurstRAM BlockPlanner DescriptorSpace Schedule Compression SourceTransport SourceOnline
  CopyIncidence
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- The scheduled visit that copies column c from the selected refresh output into the next
incidence directory. -/
abbrev visit (c : Fin 6) := RefreshBlockPlan.copyColumn B (BlockProgram.geometry B) S.steps
    (RefreshBlockPlan.input (BlockProgram.geometry B) S.steps (0 : Fin 6)) c
/-- The six column-copy visits in increasing column order. -/
abbrev visits := List.ofFn (visit B)
/-- The contiguous interval of the block script occupied by the six refresh output copies. -/
abbrev window : Window (BlockProgram.script B) (visits B) := BlockGroups.refresh B 2

variable {w g : ℕ} (base : Word w) (positions blocks t : ℕ) (Y : State (S.degreeExponent 0) g)
  (T U : IncidenceDirectory w)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Ports.data pt
local notation "first" => Script.levelsPerBlock scr * t
local notation "st" => (levelStart L (first) : Word w)
local notation "head" => levelStart L 0
local notation "dataRegion" => Window.operandRegion scr L base

/-- Certifies the copy visit's row count, source and destination operand bank, and the region
from which its planner may read. -/
structure Operands (m : Memory w) (c : Fin 6) : Prop where
  stop : (visit B c).stop.eval pub st m = (rows Y c : Word w)
  bank : ∀ i : Fin 3, ((visit B c).params i).eval pub st m = copyPublic (T.column c) (U.column c) i
  supported : HeaderOperands.Supported dataRegion pub st m (visit B c)

open private row_spec from OAI.Computability.VPVNP.CompressorRecordsCopyIncidence

private theorem scanned (src dst : Word w) (j n : ℕ) (m : Memory w) :
    StageFrame.Scanned j (j + n) (scan src dst j n m) := by
  induction n generalizing j m with
  | zero => exact .done _
  | succ n ih =>
    refine .next (by omega) (row_spec src dst j m).2.1 ?_
    simpa only [show j + 1 + n = j + (n + 1) by omega] using ih (j + 1) (after m
      (row src dst j m).events)

private theorem column_access (m : Memory w) (c : Fin 6)
    (roomT : ∀ c, (T.column c).val + rows Y c ≤ 2 ^ w) (roomU : ∀ c,
      (U.column c).val + rows Y c ≤ 2 ^ w) :
    LogAccess (ColumnCell Y T) (ColumnCell Y U) (columnScan Y T U c m) := by
  simpa only [reports, List.append_nil] using (reports_run Y T U [c] m).footprint roomT roomU

/-- Evaluate the chronological columns in their actual input memories. The
source and successor headers are below the copied cells throughout the run. -/
theorem raw (m : Memory w) (boundary : ℕ) (headBefore : head ≤ boundary)
    (roomT : ∀ c, (T.column c).val + rows Y c ≤ 2 ^ w) (roomU : ∀ c,
      (U.column c).val + rows Y c ≤ 2 ^ w)
    (fit : ∀ c, rows Y c < 2 ^ w)
    (source : ∀ x, ColumnCell Y T x → head ≤ x) (destination : ∀ x, ColumnCell Y U x → boundary ≤ x)
    (operands : ∀ mem : Memory w, (∀ x < boundary, mem x = m x) →
      ∀ c, Operands B base positions blocks t Y T U mem c) :
    SourceWalk (Window.Raw (A := scr) L base t 12) (visits B) m (reports Y T U allColumns m) := by
  have loop (cs : List (Fin 6)) (mem : Memory w) (retained : ∀ x < boundary, mem x = m x) :
      SourceWalk (Window.Raw (A := scr) L base t 12) (cs.map (visit B)) mem
        (reports Y T U cs mem) := by
    induction cs generalizing mem with
    | nil => exact .done _
    | cons c cs ih =>
      let rs := columnScan Y T U c mem
      have access := column_access Y T U mem c roomT roomU
      have op := operands mem retained c
      have initial : (visit B c).initial.eval pub st mem = 0 := rfl
      have native := (scan_native (T.column c) (U.column c) 0 (rows Y c) mem).1
      refine .next (rs := rs) ⟨12, List.replicate (rows Y c) [], le_rfl, ?_, op.supported⟩
        (ih _ (fun x hx => (after_outside mem access.2 (fun h =>
          (destination x h).not_gt hx)).trans (retained x hx)))
      refine ⟨by decide, ?_, ?_, fun a v h => source _ (access.1 a v h),
        fun a v h => headBefore.trans (destination _ (access.2 a v h))⟩
      · change runSegment (copyPass.table.instantiate w (fun i =>
        ((visit B c).params i).eval pub st mem)).program
          12 (some ((visit B c).initial.eval pub st mem)) mem _ = _
        rw [funext op.bank, initial]
        exact native
      · rw [op.stop, initial]
        simpa only [rs, columnScan, Nat.zero_add, Nat.cast_zero] using
          (scanned (T.column c) (U.column c) 0 (rows Y c) mem).toProgress (by simpa using fit c)
  have order : (allColumns.map (visit B)) = visits B := rfl
  exact order ▸ loop allColumns m (fun _ _ => rfl)

/-- Attach the six checked copies at their global program ordinals and retain
the exact reports whose post-memory contains the canonical successor graph. -/
theorem group_of_operands (m : Memory w) (boundary cap : ℕ) (ht : t < blocks)
    (endFit : endAddress L < 2 ^ w) (rowsCell : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory - 1).val = (levelWords L : Word w)) (clock : scanCap scr 12 ≤ cap)
    (headBefore : head ≤ boundary) (roomT : ∀ c, (T.column c).val + rows Y c ≤ 2 ^ w)
    (roomU : ∀ c, (U.column c).val + rows Y c ≤ 2 ^ w) (fit : ∀ c, rows Y c < 2 ^ w)
    (source : ∀ x, ColumnCell Y T x → head ≤ x) (destination : ∀ x, ColumnCell Y U x → boundary ≤ x)
    (operands : ∀ mem : Memory w, (∀ x < boundary, mem x = m x) →
      ∀ c, Operands B base positions blocks t Y T U mem c) :
    ∃ ps : List (Packet scr w), Group scr L base cap
      ((scr).initial.length + t * (scr).block.length + (window B).before.length)
        (directoryRows L) m ps ∧
      ps.map (fun p => p.stage.phase) = (window B).indices ∧
      ps.flatMap SourceWalk.Packet.reports = reports Y T U allColumns m := by
  have Hfit : head < 2 ^ w := (levelStart_mono L (Nat.zero_le _)).trans_lt endFit
  have bounds (j : Fin (scr).size) := SourceOnline.scanCap_clocks
    (p := ⟨HeaderPacket.attach scr j pub st m 12 [], m, []⟩) 12 le_rfl clock
  have live (j : Fin (visits B).length) : Window.ordinal (A := scr) t
    ((window B).index j) < directoryRows L := by
    rw [(window B).ordinal_index, BlockProgram.directory_rows, (scr).calendar_total]
    have pos := ((window B).position j).isLt
    have mul := Nat.mul_le_mul_right (scr).block.length ht
    rw [Nat.succ_mul] at mul
    omega
  exact (window B).group L base t rfl rfl Hfit cap 12 m _ (raw B base positions blocks t Y T U m
    boundary
    headBefore roomT roomU fit source destination operands) rowsCell pitch live
    (fun j _ => (bounds j).1) (fun j _ => (bounds j).2)

end CompressorRecords.RefreshCopyPackets

end

end VPVNP
end Computability
end OAI
