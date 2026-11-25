import OAI.Computability.BorderVNP.DiagonalBootedProfilePublication
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

/-! # Reading the actual independently selected epoch and public writer memory -/

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

/-- An original preparation may enumerate its epoch and directory independently
from the physical publication certificate. Their actual memories still carry
the same private placement, complete run's pin inputs and 81 signed fields. -/
theorem PublishedPin.actual_readback
    (sources : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields
      pub mac v postPin pinMem preRegs prePlace usedPin profCost)
    (epoch : Returns epochPlacement pub mac postPin pinMem)
    (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2) :
    let mid := epoch.val.2.2
    let lastMem := published.val.2.2
    let pp := Directory.ISA.placement (readings mid) (loc).raw
    let lp := Directory.ISA.placement (readings mid) (tabs).livePairs
    lastMem=Directory.ISA.publish mid a.frame a.next (dir.directory pp lp) ∧
      (loc).Image (readings prePlace) dir.entries (readings mid) ∧
      ProfileRouteInputs fields f pub (Pins.extendGuess v) lastMem ∧ BootPins pub f packet.extension hdr lastMem := by
  obtain ⟨e,p,mid,lastMem,placed,atPub,firstEmpty,secondEmpty,_,written,_,image,routed,booted,_⟩ := sources
  have first := SignedPrep.return_eq_of_empty pub mac (show epochPlacement.nativeOnly=true by decide) e epoch firstEmpty
  subst epoch
  have second := SignedPrep.return_eq_of_empty pub mac (show Directory.ISA.program.nativeOnly=true by decide) p published secondEmpty
  subst published
  subst mid
  subst lastMem
  exact ⟨written,image,routed,booted⟩

/-- The separately selected site's real middle RAM carries the frozen private
placement, and its actual pre-placement geometry fits the word. -/
theorem PublishedPin.private_geometry
    (sources : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields
      pub mac v postPin pinMem preRegs prePlace usedPin profCost)
    (epoch : Returns epochPlacement pub mac postPin pinMem)
    (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
    (mid : Memory w) (actual : epoch.val.2.2=mid) :
    (loc).Fits w (readings prePlace) ∧ (loc).Image (readings prePlace) dir.entries (readings mid) := by
  have readback := PublishedPin.actual_readback task dir N cell edgeID portID original live a u slot packet origin
    gap f hdr fields pub mac v postPin pinMem preRegs prePlace usedPin profCost sources epoch published
  obtain ⟨_,_,_,_,_,_,_,_,_,_,fitted,_⟩ := sources
  exact ⟨fitted,actual ▸ readback.2.1⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
