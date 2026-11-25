import OAI.Computability.BorderVNP.DiagonalCandidateSlottedEntry
import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart

/-! # The actual public frame of a registered placement and writer -/

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
    (postPin : Bank w) (pinMem : Memory w)

variable {R X baseFrame : ℕ} {pp lp : ℕ → ℕ × ℕ} {word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration task.cube.n task.cube.header.d}
    {group : Fin task.cube.header.d → Fin (R+1)} {guesses : ℕ → Bool}
    {I A : Type} [Fintype I] {host : I → Fin task.cube.cells} {ids : I ↪ ℕ} {size : I → ℕ}
    {recv : A → Fin task.cube.cells} {amount : A → ℕ}
    (site : SignedPrep.CandidateSite (X:=X) task.cube dir pp lp word owner decl group baseFrame a.next
      (a.operands u slot packet).layout fields f guesses pub mac postPin pinMem host ids size N cell recv amount)


variable {task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields pub mac v postPin pinMem}

/-- At the registered public operand the original middle memory carries both
placement tables and the published writer. The startup frame read is retained
as an equality, so the physical layout is indexed by the exact public word. -/
theorem PublishedPin.candidate_writer_at_operand
    (sources : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields
      pub mac v postPin pinMem site.geometryRegs site.geometry site.used site.profileCost)
    (frameAt : (pub 0).val = a.frame) :
    let layout := privateLayout (pub 0).val origin task.cube.cables task.cube.cells dir.entries dir.description gap
    let pp := Directory.ISA.placement (readings site.middle) layout.raw
    let lp := Directory.ISA.placement (readings site.middle) (bases origin task.cube.cables task.cube.cells dir.entries).livePairs
    site.published.val.2.2 = Directory.ISA.publish site.middle (pub 0).val a.next (dir.directory pp lp) ∧
    layout.Fits w (readings site.geometry) ∧ layout.Image (readings site.geometry) dir.entries (readings site.middle) ∧
    Nonempty (SlottedWriter task.cube dir pp lp (a.operands u slot packet).layout pub site.middle a.next
      (Sum.elim (Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells))
        (cell ∘ original)) (numbered (reserveID (C:=task.cube.cells) (suppliedID N cell edgeID portID)))
      (Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)) (fun _ => dir.description))) := by
  simpa only [frameAt] using (PublishedPin.candidate_writer_entry site sources)

end PackedHistoryCircuit

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA CellMacro.Generator Packing.RoutingOutputs
open BorderVNP.TeamContraction

variable {R r t d link inner n w : ℕ} {Edge : Type} {gen : Fragment IO} {G : Wiring R r t d link inner n Edge}
    {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {u : Fin (R+1)}
    (boot : BootedPinStart gen G pub reg args pin ext u)

/-- The original returned prefix reads the physical team's public operand function. -/
theorem start_public_words : boot.start.pub = pub u := rfl

/-- Transfer the actual startup address to word zero of this returned prefix. -/
theorem start_frame_of_public {frame : ℕ} (h : (pub u 0).val = frame) :
    (boot.start.pub 0).val = frame := h

/-- Read the routing header at word zero of this very returned prefix. -/
theorem start_routing_header {origin edges cells entries : ℕ} {mem : ℕ → ℕ}
    (h : Header (pub u 0).val origin edges cells entries mem) :
    Header (boot.start.pub 0).val origin edges cells entries mem := h

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
