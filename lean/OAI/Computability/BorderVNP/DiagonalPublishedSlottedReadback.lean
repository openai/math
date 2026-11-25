import OAI.Computability.BorderVNP.DiagonalPublishedControlReadback
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

/-! # Recovering the native slotted writer on the returned directory -/

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

local notation "loc" => privateLayout a.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation "tabs" => bases origin task.cube.cables task.cube.cells dir.entries
set_option maxHeartbeats 1450000

/-- Recover the actual placement, room, and native slotted writer from a
profile's physical publication, even when the candidate stores the common
mathematical placement for its later scheduler. -/
theorem PublishedPin.actual_slotted
    (sources : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields
      pub mac v postPin pinMem preRegs prePlace usedPin profCost)
    (epoch : Returns epochPlacement pub mac postPin pinMem)
    (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2) :
    let mid := epoch.val.2.2
    let pp := Directory.ISA.placement (readings mid) (loc).raw
    let lp := Directory.ISA.placement (readings mid) (tabs).livePairs
    published.val.2.2=Directory.ISA.publish mid a.frame a.next (dir.directory pp lp) ∧
    (loc).Fits w (readings prePlace) ∧ (loc).Image (readings prePlace) dir.entries (readings mid) ∧
    Nonempty (SlottedWriter task.cube dir pp lp (a.operands u slot packet).layout pub mid a.next
      (Sum.elim (Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells))
        (cell ∘ original))
      (numbered (reserveID (C:=task.cube.cells) (suppliedID N cell edgeID portID)))
      (Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)) (fun _ => dir.description))) := by
  obtain ⟨e,p,mid,last,placed,atPub,empty,empty₂,_,written,fit,image,_,_,_,_,⟨writer,_⟩,_⟩ := sources
  have first := SignedPrep.return_eq_of_empty pub mac (show epochPlacement.nativeOnly=true by decide) e epoch empty
  subst epoch
  have second := SignedPrep.return_eq_of_empty pub mac (show Directory.ISA.program.nativeOnly=true by decide) p published empty₂
  subst published
  subst mid
  subst last
  exact ⟨written,fit,image,⟨writer⟩⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
