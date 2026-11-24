import OAI.Computability.VPVNP.PairSimulationWorkerControl
import OAI.Computability.VPVNP.PairVertexOrdinalPhase

/-! # The vertex memory frame along successful prefixes of the terminal program -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM CompressorRecords TerminalLink
open scoped Fin.CommRing

variable {w n g cap base grammar : ℕ} {pub : Fin 11 → Word w} {D : IndexedSites n g}
    {geometry rootFields leaf shrink refresh : Segment}
local notation "S" => segments geometry rootFields leaf shrink refresh
local notation "P" => Machine.program (Template.instantiate (template S) w pub)
local notation "Frame" => VertexFrame.Linked (TerminalLink.header pub) base grammar g

/-- Each successful vertex call preserves the protected address, including on a
prefix that never reaches the closing ordinal. A continuing call advances the
ordinal and preserves the linked frame after the controller stores its result. -/
def ordinalWorkerControl (F : DescriptorSpace.Shape) (limit : ℕ) (ref phy : Memory w) (a : ℕ)
    (H : ActiveCalls D P cap base grammar (Frame ref))
    (close : Closes P cap n pub (Frame ref))
    (outside : a < base + grammar ∨ base + grammar + g ≤ a)
    (cell : workerCell (TerminalLink.header pub) a) (ready : Frame ref 0 phy) :
    WorkerControl (TerminalProgram.workers F limit S) pub cap .vertices a phy where
  inv st m := ∃ j : ℕ, j ≤ n ∧ st = (j : Word w) ∧ Frame ref j m
  ready := ⟨0, Nat.zero_le _, rfl, ready⟩
  advance st m bits raw inv run := by
    obtain ⟨j, le, rfl, linked⟩ := inv
    let e := Entry.resume Stage.vertices (j : Word w)
    have full := execute_extend run (cap - rawFuel pub cap e)
    rw [Nat.add_sub_of_le (show rawFuel pub cap e ≤ cap from Nat.sub_le ..)] at full
    change execute P cap (Program.start P (j : Word w)) m bits = some raw at full
    rcases lt_or_eq_of_le le with lt | rfl
    · let i : Fin n := ⟨j, lt⟩
      obtain ⟨x, rfl⟩ := H.recover i m linked bits raw full
      obtain ⟨rep, call, next, flush⟩ := H.emit i m linked x
      obtain rfl := Option.some.inj (full.symm.trans call)
      have post := linked.report e raw (D.powers i x) flush
      refine ⟨(post a outside cell).trans (linked a outside cell).symm, ?_⟩
      intro st' returned
      exact ⟨j + 1, lt, Option.some.inj (returned.symm.trans next), post⟩
    · rw [close m linked] at full
      split at full
      · obtain rfl := Option.some.inj full
        have post := VertexFrame.Linked.after_report (raw := closingReport pub m) e
          (closingReport_after pub m ▸ linked)
        exact ⟨(post a outside cell).trans (linked a outside cell).symm, fun _ h => nomatch h⟩
      · contradiction

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
