import OAI.Computability.BorderVNP.DiagonalPinnedPlacementKeys
import OAI.Computability.BorderVNP.DiagonalPublishedSlottedReadback

/-! # The occupied placement keys and canonical writer on a returned calendar pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank LocalRow BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open Packing.RoutingOutputs.NativeDemands
open scoped Classical

open CellMacro.Generator RoutingISA.CompactMachine PackedHistoryCircuit

variable {D p w d g : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (task : SignedTaskArena.Layout) (dir : Directory.Layout) (N : Network D P bits)
    (cell : N.Site → Fin task.cube.cells) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d) (origin gap : ℕ)
    (f : BroadcastFrame) (hdr : List Bool) (fields : Pins.ProcessorFields (a.operands u slot packet).layout)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (v : Fin g → Bool)
    (postPin : Bank w) (pinMem : Memory w) (preRegs : Bank w) (prePlace : Memory w) (usedPin profCost : ℕ)

local notation "loc" => privateLayout a.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation "tabs" => bases origin task.cube.cables task.cube.cells dir.entries
set_option maxHeartbeats 1450000

local notation3 (prettyPrint := false) "canonP" => NativeDemands.privatePair N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "canonL" => NativeDemands.livePair N cell edgeID portID dir original live gap

/-- The actual pin geometry and the chosen epoch/directory returns give the
semantic placement keys, the native writer using those keys, and the precise
published memory. Only occupied keys are compared. -/
theorem PublishedPin.canonicalSlottedReturn
    (pin : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields pub mac
      v postPin pinMem preRegs prePlace usedPin profCost)
    (epoch : Returns epochPlacement pub mac postPin pinMem)
    (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
    {ns cb lb wb : ℕ} {σ : Type} [Fintype σ] (aux : N.Site → ℕ) (ids : N.Site ↪ Fin ns)
    (geom : Fields ns task.cube.cables p task.cube.cells cb lb wb σ) (x : σ → Bool)
    (rep : Packing.CellAddressPhysical.Represents N cell aux ids edgeID portID geom x) (cells : ∀ c,(geom.cells c).val=c.val)
    (width : ∀ j,bits (live j)=dir.block)
    (small : ∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^wb)
    (image : Image geom (ids ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings prePlace))
    (bounds : dir.DestinationBounds) :
    let mid := epoch.val.2.2
    let old := Directory.ISA.placement (readings mid) (loc).raw
    let resident := Directory.ISA.placement (readings mid) (tabs).livePairs
    (∀ j,dir.keyPlacement old resident j=dir.keyPlacement canonP canonL j) ∧
      published.val.2.2=Directory.ISA.publish mid a.frame a.next (dir.directory canonP canonL) ∧
      Nonempty (SlottedWriter task.cube dir canonP canonL (a.operands u slot packet).layout pub mid a.next
        (Sum.elim (Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells))
          (cell ∘ original))
        (numbered (reserveID (C:=task.cube.cells) (suppliedID N cell edgeID portID)))
        (Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)) (fun _ => dir.description))) := by
  intro mid old resident
  obtain ⟨actual,fit,placed,⟨writer⟩⟩ := PublishedPin.actual_slotted task dir N cell edgeID portID original live a u slot
    packet origin gap f hdr fields pub mac v postPin pinMem preRegs prePlace usedPin profCost pin epoch published
  have keys := NativeDemands.returned_key_placements N cell edgeID portID dir original live gap width aux ids geom x
    rep cells small a.frame origin (readings prePlace) (readings mid) image placed fit
  have same (j : dir.DestinationKey) : dir.keyPlacement old resident j=dir.keyPlacement canonP canonL j := (keys j).symm
  exact ⟨same,actual.trans (congrArg (Directory.ISA.publish mid a.frame a.next)
    (dir.directory_congr_keys old resident canonP canonL bounds same)),⟨writer.withKeyPlacements same⟩⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
