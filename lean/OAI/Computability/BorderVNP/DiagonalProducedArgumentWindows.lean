import OAI.Computability.BorderVNP.DiagonalProducedArgumentCells
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomStride

/-! # The actual emitted task fits the physical signed argument windows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch CompactMachine CellSparse CellPacket TypedTaskBuilder
open CellPacket.Supplement.Batch

variable {w n : ℕ} {Site : Type} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (a : SignedTaskArena.Layout) (l : CellControlRows.Layout) (raw : ℕ → ℕ)
    (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record) (cells : ℕ → SparseExterior.Owned)

/-- The unpacked payload at the compact ordinal has the actual selected
private-cell directory, private width and physical compact exterior. -/
theorem produced_call_payload (j : ℕ) :
    let i := globalCell l.toLayout raw j
    let row := produced l raw p geom extra j
    let layout := SparseExterior.batchLayout a l.frame l.control (l.before raw l.cells)
    let input := SparseExterior.logicalCell (p i) (extra i) (cells i).field
    ((cells i).typed layout row.typed).cell.payload =
      Packet.input input.directory input.privateWires (cells i).field.bytes := by
  intro i row layout input
  exact congrArg (fun packet => RationalHitting.StackLanguage.codeWord packet ++ (cells i).field.bytes)
    (SparseExterior.supplemented_packet (l.atCell raw p i) (extra i) (cellLayout l raw i) (geom i))

/-- The physical compaction bound on each owned cell pays directly for the
unpacked scratch bytes and the burst words of each produced typed argument. -/
theorem produced_call_windows {n w : ℕ} (hn : 1≤n) (hw : 0<w) (hW : w≤n)
    (scratch : SignedTaskArena.scratchWindow n≤a.p.scratchStride)
    (burst : SignedTaskArena.burstWindow n≤a.p.burstStride)
    (cap : ∀ c < l.cells, l.owner raw c=l.team →
      let input := SparseExterior.logicalCell (p c) (extra c) (cells c).field
      (CompactFrame.pack w (Packet.input input.directory input.privateWires (cells c).field.bytes)).length ≤ TeamScales.width n (1/2)) :
    let layout := SparseExterior.batchLayout a l.frame l.control (l.before raw l.cells)
    ∀ j < l.before raw l.cells, let i := globalCell l.toLayout raw j
      let task := ((cells i).typed layout (produced l raw p geom extra j).typed).cell
      task.payload.length≤a.p.scratchStride ∧ (task.burst w).length≤a.p.burstStride := by
  intro layout j hj i task
  have index := global_spec l.toLayout raw hj
  have allowance := cap i index.1 index.2.1
  let input := SparseExterior.logicalCell (p i) (extra i) (cells i).field
  have rooms := SignedTaskArena.windows_of_packet input.directory (cells i).field hn hw hW allowance
  exact ⟨(congrArg List.length (produced_call_payload a l raw p geom extra cells j)).le.trans (rooms.2.1.trans scratch),
    (congrArg List.length (produced_call_burst (w:=w) a l raw p geom extra cells j)).le.trans (rooms.2.2.trans burst)⟩

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
