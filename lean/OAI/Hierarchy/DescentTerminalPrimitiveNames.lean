import OAI.Hierarchy.DescentTerminalPassNames
import OAI.Hierarchy.DescentTerminalPrimitivePair
import OAI.Hierarchy.DescentTerminalPointerPair
import OAI.Hierarchy.DescentTerminalCountWidthPair
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Instruction names and clocks for the six native terminal field passes -/
namespace Hierarchy.DescentTerminalPrimitiveNames
open DescentSIMDLookup DescentTerminalCombinedRole DescentTerminalPointerDigits ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentStaticWordColumn (names names_seq names_scan names_mount)
noncomputable section

variable {L blocks d u v : ℕ}

private theorem name_frame (w base H : ℕ) (src : Fin L → Bank) (f : (Fin L → Cell d) → Cell u) :
    names (DescentTerminalPointerFrame.program w base src H f) =
      15 * (DescentTerminalPointerFrame.size L d + 1) + (35 + 52 * L) := by
  simp only [DescentTerminalPointerFrame.program, DescentTerminalPointerFrame.mount,
    names_seq, names_mount, names_scan, DescentTerminalPointerFrame.row_work]
  omega

private theorem cheap_frame (w base H : ℕ) (src : Fin L → Bank) (f : (Fin L → Cell d) → Cell u) :
    CheapCode (DescentTerminalPointerFrame.program w base src H f) :=
  cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@scan_cheap _ _ _ _)

private theorem read_work (chart : Fin L → Fin blocks → Gather.Address) (j : ℕ) :
    (Gather.flattened chart j).work ≤ 7 := by
  have one (a : Gather.Address) : a.expr.work ≤ 7 := by cases a <;> simp [Gather.Address.expr, Expr.work]
  unfold Gather.flattened
  split
  · exact one _
  · decide

variable (w : ℕ) (first second : Shelf) (roleOut origin shops : ℕ)
  (chart : Fin L → Fin blocks → Gather.Address)
  (f0 : (Fin L → Cell d) → Cell u) (f7 : (Fin L → Cell d) → Cell v)
  (source : Fin 3 → Bank) (dc countBase widthBase q hid N A groups p : ℕ)
local notation "rows" => blocks * shops
local notation "preads" => Gather.dropOff origin blocks shops L chart
local notation "src" => Gather.banks (L := L) origin rows
local notation "base₀" => Gather.rom origin L rows
local notation "s0" => DescentTerminalPointerFrame.size L d
local notation "s2" => DescentTerminalPointerFrame.size 3 dc
local notation "base₇" => base₀ + s0 + rows
local notation "p0" => DescentTerminalPointerFrame.program w base₀ src rows f0
local notation "p7" => DescentTerminalPointerFrame.program w base₇ src rows f7
local notation "lastPair" => DescentTerminalCountWidthPair.program w dc q hid N A groups blocks shops p countBase widthBase source
local notation "rolePair" => paired (wb := w) first second roleOut rows

/-- The procedure sequence used by the normalized six-field receipt. -/
def program := (rolePair).seq ((((ProtocolRAM.program w preads).seq p0).seq p7).seq lastPair)
local notation "machine" => program w first second roleOut origin shops chart f0 f7 source dc countBase widthBase q hid N A groups p

theorem cheap : CheapCode machine :=
  cheap_seq (cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _))
    (cheap_seq (cheap_seq (cheap_seq (@ProtocolRAM.program_cheap _ _) (@cheap_frame _ _ _ _ _ _ _ _)) (@cheap_frame _ _ _ _ _ _ _ _))
      (cheap_seq (@cheap_frame _ _ _ _ _ _ _ _) (@scan_cheap _ _ _ _)))

/-- Both role scans, the gather, three ROM installations, their scans, and the width scan. -/
theorem names_exact : names machine =
    1030 + 104 * L + 15 * (2 * s0 + s2) + readNames preads := by
  simp only [program, paired, DescentTerminalCountWidthPair.program,
    DescentTerminalCountWidthPair.countProgram, DescentTerminalIssuedWidths.program, names_seq,
    name_frame, names_scan, DescentTerminalCombinedRole.work, schedule_names,
    DescentTerminalIssuedWidths.literal, Expr.work]
  ring

theorem names_le : names machine ≤
    1030 + 104 * L + 15 * (2 * s0 + s2) + 39 * (L * blocks) := by
  rw [names_exact]
  exact Nat.add_le_add_left (batch_names_le 7 origin shops shops _ (read_work chart) 0 (L * blocks)) _

local notation "oneFrame" => (4 + 10 * s0) + (4 + rows * (16 + 26 * L))
/-- Exact clocks in the normalized six-field execution receipt. -/
def clocks (d dc origin shops : ℕ) (chart : Fin L → Fin blocks → Gather.Address) :=
  let n := blocks * shops
  let size := DescentTerminalPointerFrame.size L d
  let pass := (4 + 10 * size) + (4 + n * (16 + 26 * L))
  (steps n + steps n) + (((ProtocolRAM.clock (Gather.dropOff origin blocks shops L chart) + pass) + pass) +
    DescentTerminalCountWidthPair.clocks dc blocks shops)

theorem clocks_le : clocks d dc origin shops chart ≤
    40 + 10 * (2 * s0 + s2) + 4 * (L * blocks) + rows * (476 + 70 * L) := by
  have read := DescentPackedFlowBatch.tariff origin shops shops (L * blocks) (Gather.flattened chart) 7
    (fun j _ => read_work chart j)
  change ProtocolRAM.clock preads ≤ 4 + (L * blocks) * (4 + shops * 18) at read
  unfold clocks DescentTerminalCountWidthPair.clocks steps
  dsimp only
  calc
    _ ≤ ((4 + 172 * rows) + (4 + 172 * rows)) +
      ((((4 + (L * blocks) * (4 + shops * 18)) + oneFrame) + oneFrame) +
        (((4 + 10 * s2) + (4 + rows * (16 + 26 * 3))) + (4 + rows * 6))) := by gcongr
    _ = _ := by ring

/-- A separately installed run-independent role-and-arity dictionary contributes its names once. -/
theorem names_with_role_table (base n : ℕ) (data : ℕ → ℕ) :
    names ((DescentStaticWordColumn.program w base data n).seq machine) ≤
      15 * (n + 1) + (1030 + 104 * L + 15 * (2 * s0 + s2) + 39 * (L * blocks)) := by
  rw [names_seq, names_mount]
  exact Nat.add_le_add_left (names_le ..) _


end
end Hierarchy.DescentTerminalPrimitiveNames

end OAI
