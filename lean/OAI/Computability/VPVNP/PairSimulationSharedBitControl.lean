import OAI.Computability.VPVNP.PairSimulationFinalBitScan
import OAI.Computability.VPVNP.PairSimulationWorkerControl

/-!
# Shared-bit frames along partial native runs

The shared-bit worker can write only one wire per data call. Its ordinary
header words survive both that write and the controller's two handoff writes.
This invariant covers any successful prefix of the terminal program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.FinalBits.Worker

open BurstRAM PrivateRAM CompressorRecords LiveProgram
open scoped Fin.CommRing

variable {w : ℕ} {pub : Fin 11 → Word w} {lo count : ℕ}

open private field_away active_at next_layout from OAI.Computability.VPVNP.PairSimulationFinalBitScan
open private report_agree from OAI.Computability.VPVNP.PairSimulationTerminalSplice

private theorem layout_transfer {src phy : Memory w} (h : Layout pub src lo count)
    (room : (header pub).val + 32 ≤ 2 ^ w)
    (agree : SourceTransport.Agree (TerminalLink.workerCell (header pub)) src phy) :
    Layout pub phy lo count := by
  refine ⟨?_, ?_, h.fits, h.base_disjoint, h.total_disjoint⟩
  · exact (agree _ (field_away pub room 13 (by decide) (by decide))).symm.trans h.base_eq
  · exact (agree _ (field_away pub room 12 (by decide) (by decide))).symm.trans h.total_eq

private theorem successful_call (st : Word w) (m : Memory w) {fuel : ℕ} {bits : List Bool}
    {r : Report w} (run : execute (table.instantiate w pub).program fuel
      ((table.instantiate w pub).program.start st) m bits = some r) :
    (st < total pub m ∧ ∃ b, r = activeReport pub st m b) ∨ r = closeReport pub m := by
  have extended := execute_extend run 24
  rcases lt_trichotomy st (total pub m) with hi | hi | hi
  · rw [active pub st m hi] at extended
    cases bits with
    | nil => contradiction
    | cons b bs =>
      cases bs with
      | cons => contradiction
      | nil => exact .inl ⟨hi, b, (Option.some.inj extended).symm⟩
  · rw [close pub st m hi] at extended
    split at extended <;> try contradiction
    exact .inr (Option.some.inj extended).symm
  · rw [overrun pub st m hi] at extended
    contradiction

private theorem active_step (st : Word w) (m : Memory w) (h : Layout pub m lo count)
    (live : st < total pub m) (b : Bool) {a : ℕ} (outside : a < lo ∨ lo + count ≤ a) :
    let raw := after m (activeReport pub st m b).events
    raw a = m a ∧ Layout pub raw lo count := by
  have fit := h.fits
  have hst : st.val < count := by
    rw [h.total_eq] at live
    change st.val < count % (2 ^ w) at live
    rwa [Nat.mod_eq_of_lt (by omega)] at live
  let j := count - st.val - 1
  have splitCount : st.val + (j + 1) = count := by dsimp [j]; omega
  have dest : address pub m st = cursor w lo j := by
    simpa only [Fin.cast_val_eq_self] using (active_at h splitCount).2
  have inside : (cursor w lo j).val = lo + j := Nat.mod_eq_of_lt (by omega)
  have ne : a ≠ (address pub m st).val := by rw [dest, inside]; omega
  exact ⟨by simp only [active_image, writeMemory, ite_eq_right ne],
    by simpa only [Fin.cast_val_eq_self] using next_layout h splitCount b⟩

/-- Every successful shared-bit burst preserves an address outside both the
wire bank and the terminal controller cells. The invariant starts at the
actual physical memory left by the row phase. -/
def control (workers : TerminalLink.Stage → PairTable)
    (bank : workers TerminalLink.Stage.sharedBits = ⟨28, 5, table⟩)
    (cap a : ℕ) (src phy : Memory w) (layout : Layout pub src lo count)
    (room : (header pub).val + 32 ≤ 2 ^ w)
    (agree : SourceTransport.Agree (TerminalLink.workerCell (header pub)) src phy)
    (outside : a < lo ∨ lo + count ≤ a) (cell : TerminalLink.workerCell (header pub) a) :
    TerminalLink.WorkerControl workers pub cap TerminalLink.Stage.sharedBits a phy where
  inv _ m := Layout pub m lo count
  ready := layout_transfer layout room agree
  advance st m bits rep h run := by
    unfold TerminalLink.source at run
    rw [bank] at run
    have agreeOut := report_agree (header pub) (.resume TerminalLink.Stage.sharedBits st) rep m m
      (fun _ _ => rfl)
    have frame := (agreeOut a cell).symm
    obtain ⟨live, b, rfl⟩ | rfl := successful_call st m run
    · obtain ⟨rawFrame, rawLayout⟩ := active_step st m h live b outside
      exact ⟨frame.trans rawFrame, fun _ _ => layout_transfer rawLayout room agreeOut⟩
    · exact ⟨frame.trans (congrFun (close_image pub m) a), fun _ impossible => by
        simp only [close_result, reduceCtorEq] at impossible⟩

end PairSimulation.FinalBits.Worker

end VPVNP
end Computability
end OAI
