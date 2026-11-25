import OAI.Computability.BorderVNP.DiagonalPublishedSlottedReadback
import OAI.Computability.BorderVNP.DiagonalSignedCandidateSite
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

/-! # The native placement recovered for any selected signed candidate -/

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

local notation3 (prettyPrint := false) "pr" => privateLayout a.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tabs" => bases origin task.cube.cables task.cube.cells dir.entries

/-- Recover the native (possibly noncanonical on unused table entries)
writer on the candidate's own chronological first two returns. -/
theorem PublishedPin.candidate_geometry
    (sources : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields
      pub mac v postPin pinMem site.geometryRegs site.geometry site.used site.profileCost) :
    (pr).Image (readings site.geometry) dir.entries (readings site.middle) ∧
    (pr).Fits w (readings site.geometry) ∧
    Nonempty (SlottedWriter task.cube dir (Directory.ISA.placement (readings site.middle) (pr).raw)
      (Directory.ISA.placement (readings site.middle) (tabs).livePairs) (a.operands u slot packet).layout pub site.middle a.next
      (Sum.elim (Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells))
        (cell ∘ original)) (numbered (reserveID (C:=task.cube.cells) (suppliedID N cell edgeID portID)))
      (Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)) (fun _ => dir.description))) := by
  have raw := PublishedPin.actual_slotted task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields
    pub mac v postPin pinMem site.geometryRegs site.geometry site.used site.profileCost sources site.epoch site.published
  obtain ⟨_,fit,placed,writer⟩ := raw
  exact ⟨by simpa only [site.epochMemory] using placed,fit,by simpa only [site.epochMemory] using writer⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
