import OAI.Computability.BorderVNP.DiagonalCandidateSlottedFrame
import OAI.Computability.BorderVNP.DiagonalIssuedWriterRetention

/-! # The physical writer at the public operand of an original team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit



open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank LocalRow BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open scoped Classical

open CellMacro.Generator RoutingISA.CompactMachine PackedHistoryCircuit

variable {D p w d g : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (task : SignedTaskArena.Layout) (dir : Directory.Layout) (N : Network D P bits)
    (cell : N.Site → Fin task.cube.cells) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d) (origin gap : ℕ)
    (f : BroadcastFrame) (hdr : List Bool) (fields : Pins.ProcessorFields (a.operands u slot packet).layout)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (v : Fin g → Bool)
    (postPin : Bank w) (pinMem : Memory w) (preRegs : Bank w) (prePlace : Memory w) (usedPin profCost : ℕ)

/-- Read the two placement arrays and their writer from the native epoch and
publication registered by this pin. The resulting locations and writer are
indexed by the public operand of the received team. -/
theorem PublishedPin.writer_at_frame_of_returns
    (sources : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields
      pub mac v postPin pinMem preRegs prePlace usedPin profCost)
    (epoch : Returns epochPlacement pub mac postPin pinMem)
    (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
    (operand : Arg → Word w) (mid : Memory w) (public_eq : operand=pub)
    (head : (operand 0).val=a.frame) (middle_eq : epoch.val.2.2=mid) :
    let loc := privateLayout (operand 0).val origin task.cube.cables task.cube.cells dir.entries dir.description gap
    let tabs := bases origin task.cube.cables task.cube.cells dir.entries
    let pp := Directory.ISA.placement (readings mid) (loc).raw
    let lp := Directory.ISA.placement (readings mid) (tabs).livePairs
    published.val.2.2=Directory.ISA.publish mid (operand 0).val a.next (dir.directory pp lp) ∧
    (loc).Fits w (readings prePlace) ∧ (loc).Image (readings prePlace) dir.entries (readings mid) ∧
    Nonempty (SlottedWriter task.cube dir pp lp (a.operands u slot packet).layout operand mid a.next
      (Sum.elim (Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells))
        (cell ∘ original))
      (numbered (reserveID (C:=task.cube.cells) (suppliedID N cell edgeID portID)))
      (Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)) (fun _ => dir.description))) := by
  subst operand
  simpa only [head, middle_eq] using
    (PublishedPin.actual_slotted task dir N cell edgeID portID original live a u slot packet origin gap f hdr
      fields pub mac v postPin pinMem preRegs prePlace usedPin profCost sources epoch published)

end PackedHistoryCircuit

namespace FiniteEvaluator.CubeAllocation

open RoutingISA Packing VPVNP.BurstRAM

/-- The issued owner retains the writer's published RAM at its physical
address after identifying the native publication with the emitted memory. -/
theorem HostRetention.at_written_memory {w head : ℕ} {ar : CubeArena.Layout}
    {published written : Memory w} {before after : ℕ → ℕ} (same : published=written)
    (kept : HostRetention ar head (readings published) before after) :
    HostRetention ar head (readings written) before after :=
  same ▸ kept

end FiniteEvaluator.CubeAllocation

end BorderVNP
end Computability
end OAI
