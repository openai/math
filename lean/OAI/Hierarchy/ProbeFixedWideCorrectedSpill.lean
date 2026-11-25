import OAI.Hierarchy.ProbeFixedWideSpillDates
import OAI.Hierarchy.ProbeFixedWideSpillTurns

namespace OAI
/-! # The single fixed post-pruning suffix for real clipped commodity paths -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width ell unitCost bits datedROM datedWork terminalROM terminalWork first : ℕ)
local notation "W" => ProbeStage.Native.wordBits h (2^v.W) ProbeStage.Native.copies
local notation "g" => v.wideDated h width ell unitCost
local notation "z" => v.wideSpillDates h width ell unitCost bits first
local notation "r" => v.wideSpillRankEnd h width bits first
local notation "t" => WideCPU.SpillDates.endAt z r
local notation "cols" => v.wide_spill_columns h width ell unitCost
local notation "old" => WideCPU.SpillDates.preClip z datedWork r
local notation "now" => fun j=>WideCPU.Dated.roleStart g datedWork (Fin.succ j)
local notation "left" => fun j=>WideCPU.SpillDates.dateRole z r j 1
local notation "right" => fun j=>WideCPU.SpillDates.dateRole z r j 2

def wideCorrectedSpillProgram : Procedure W :=
  (v.wideSpillRankProgram h width bits first).seq
   (((z).program W datedROM datedWork r cols).seq
    (v.wideSpillTurnsProgram h width bits datedROM terminalROM terminalWork first t old now left right))

def wideCorrectedSpillTicks :=
  v.wideSpillRankTicks h width bits first+((z).ticks datedROM datedWork r cols+
    v.wideSpillTurnsTicks h width bits datedROM terminalROM terminalWork first t old now left right)

def wideCorrectedSpillEnd :=
  v.wideSpillTurnsEnd h width bits datedROM terminalROM terminalWork first t old now left right

/-- Join the real quantity scan, the new source/target role tables and the
corrected chronological turns in their physical execution order. -/
theorem wide_spill_append (initial ranks sheets completed : Memory W)
    (rankRun : (v.wideSpillRankProgram h width bits first).Exec initial ranks
      (v.wideSpillRankTicks h width bits first))
    (rowRun : ((z).program W datedROM datedWork r cols).Exec ranks sheets ((z).ticks datedROM datedWork r cols))
    (turnRun : (v.wideSpillTurnsProgram h width bits datedROM terminalROM terminalWork first t old now left right).Exec
      sheets completed (v.wideSpillTurnsTicks h width bits datedROM terminalROM terminalWork first t old now left right)) :
    (v.wideCorrectedSpillProgram h width ell unitCost bits datedROM datedWork terminalROM terminalWork first).Exec
      initial completed (v.wideCorrectedSpillTicks h width ell unitCost bits datedROM datedWork terminalROM terminalWork first) :=
  rankRun.then (rowRun.then turnRun)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
