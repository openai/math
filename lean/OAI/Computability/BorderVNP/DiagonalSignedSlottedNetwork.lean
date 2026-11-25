import OAI.Computability.BorderVNP.CubeRouteProfileDataFrame
import OAI.Computability.BorderVNP.CubeRouteEmitterInputs
import OAI.Computability.BorderVNP.PackedRoutingPlaced

/-! # The signed writer at a returned network geometry and private placement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank
open scoped Classical BigOperators

private theorem placedSize {A : Type*} [Fintype A] {C E : ℕ}
    (sc : A → Fin C) (sw : A → ℕ) (old : Fin E → Fin C) (gap desc : ℕ) (c : Fin C) :
    DataSlabs.size (Sum.elim (Sum.elim sc id) old)
        (Sum.elim (Sum.elim sw (fun _ : Fin C => gap)) (fun _ : Fin E => desc)) c =
      DataSlabs.size sc sw c + gap + ∑ j, if old j=c then desc else 0 := by
  rw [← reservedSize sc sw gap c]
  change (∑ v : (A ⊕ Fin C) ⊕ Fin E, if Sum.elim (Sum.elim sc id) old v = c
    then Sum.elim (Sum.elim sw (fun _ => gap)) (fun _ => desc) v else 0) = _
  rw [Fintype.sum_sum_type]
  rfl

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1400000 in
/-- The reached physical scalar and packet frames plus the retained terminal
geometry determine the writer's real pointers and all receiving slots.
Its size counts the descriptions delivered to the specified cell. -/
noncomputable def signedSlottedWriter {D s p depth k b w d : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {σ : Type*} [Fintype σ] (task : SignedTaskArena.Layout) (dir : Directory.Layout)
    (N : Network D P bits) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
    (F : Fields s task.cube.cables p task.cube.cells depth k b σ) (x : σ → Bool)
    (net : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x) (ids : ∀ c, (F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ t, bits (live t)=dir.block) (arena : StartupArena) (u : Fin arena.teams)
    (slot : ℕ) (packet : ReferencePacket w d) (other : Arg → Word w) (origin gap : ℕ)
    {f : BroadcastFrame} {advice : AdviceLayout} {hdr : List Bool} {z : Bank w} {saved profile mid : Memory w}
    (guess : ℕ → Bool) :
    let B := arena.operands u slot packet
    let args := core (withDemandBase (task.routeBank arena.frame other) arena.next) origin task.cube.cables task.cube.cells
    let pub := B.bank args
    let pl := privateLayout arena.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
    let lo := (bases origin task.cube.cables task.cube.cells dir.entries).livePairs
    let sc := Sum.elim (fun v : SuppliedWord N cell => v.1) (id : Fin task.cube.cells → Fin task.cube.cells)
    let sw := Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)
    let si := reserveID (C := task.cube.cells) (suppliedID N cell edgeID portID)
    B.Fits w → arena.next ≤ origin → arena.next < 2^w → task.cube.records < 2^w →
    (packet.extension (41 : Fin 81)).val = task.cube.hostDirectory →
    arena.next+7*dir.candidates ≤ task.cube.header.header →
    dir.teams=arena.teams → dir.processors=arena.processors → dir.literal=arena.literal → 0<dir.fields →
    dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2) → dir.DestinationBounds →
    (∀ c, suppliedSize N cell c+gap+(∑ j, if cell (original j)=c then dir.description else 0) ≤ task.cube.cellStride) →
    ∀ {fields : Pins.ProcessorFields B.layout}, JointHeader.BootHeaderState fields f advice packet pub hdr z saved →
    (∀ j < arena.next, profile j=Pins.preparedMemory B.layout guess saved B.layout.count j) →
    Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings profile) →
    pl.Fits w (readings profile) → pl.Image (readings profile) dir.entries (readings mid) →
    SlottedWriter task.cube dir (Directory.ISA.placement (readings mid) pl.raw) (Directory.ISA.placement (readings mid) lo)
      B.layout pub mid arena.next (Sum.elim sc (cell ∘ original)) (numbered si)
      (Sum.elim sw (fun _ => dir.description)) := by
  intro B args pub pl lo sc sw si fits originLo nextFit recordsFit host rawRoom dt dp dl fieldsPos tail bound
    cap fields boot resident img fit place
  have base : (pub 0).val=arena.frame := B.frameBase_word args fits
  have pointers := slotted_dataFrame task arena u slot packet other origin task.cube.cables task.cube.cells dir.entries
    dir.description gap guess originLo nextFit recordsFit host fits boot resident place
  have placed := img.networkPlacement N cell aux siteID edgeID portID F net ids wireFit dir original live liveWidth
    arena.frame origin gap (readings profile) (readings mid) place fit
  have sep := task.cube.separated
  have headLow : task.cube.header.header ≤ task.cube.packetEnd := by
    unfold CubeArena.Layout.packetEnd CubeHeaderInstall.bankStop CubeHeaderInstall.Inputs.packetBase; omega
  have upto : arena.next ≤ task.cube.pairBase := by omega
  have lower : arena.frame+112 ≤ arena.next := by
    dsimp only [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]; omega
  refine ⟨pointers.1,?_,?_,?_,dt,fieldsPos,tail,Nat.zero_lt_of_lt u.isLt,dp,dl,?_,?_,placed,bound,?_⟩
  · rw [base]
    exact pointers.2
  · rw [base]; exact lower
  · have len := dir.directory_length_le (Directory.ISA.placement (readings mid) pl.raw) (Directory.ISA.placement (readings mid) lo)
    omega
  · have layout : B.layout.stride = arena.stride := by
      dsimp only [B, StartupArena.operands, Pins.Layout.stride, Pins.Layout.offset, StartupArena.stride]; omega
    rw [layout]
    exact (show arena.frame ≤ arena.next by omega).trans upto
  · change arena.ibase+arena.count ≤ task.cube.pairBase
    exact (show arena.ibase+arena.count ≤ arena.next by unfold StartupArena.next StartupArena.hbase; omega).trans upto
  · intro c
    rw [placedSize, dataSlabs_size]
    exact cap c

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
