import OAI.Computability.BorderVNP.DiagonalSignedDemandPublication
import OAI.Computability.BorderVNP.CubeRouteJointPacket

/-! # The true combined signed reference packet supplies the demand publisher's inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction ProcessorSlots
open Packing RoutingOutputs DiagonalResidueRAM GeometryAdvice
open scoped Classical

/-- The global demand-table address bound covers each scalar in the directory
frame, including the occupied extent and the supplied-bit block length. -/
theorem publication_dimensions {w : ℕ} (dir : Directory.Layout) (pb lb extent : ℕ)
    (fields : dir.fields≤2) (wordFit : 1<2^w)
    (room : Directory.ISA.wordBound (Directory.ISA.placementBound dir pb lb extent) < 2^w) :
    dir.entries < 2^w ∧ dir.sites < 2^w ∧ dir.block < 2^w ∧ dir.description < 2^w ∧ dir.fields-1 < 2^w := by
  let M := Directory.ISA.placementBound dir pb lb extent
  have small : M < 2^w := by
    apply lt_of_le_of_lt _ room
    change M ≤ Directory.ISA.wordBound M
    unfold Directory.ISA.wordBound
    nlinarith [Nat.zero_le (M^4),Nat.zero_le (M^3),Nat.zero_le (M^2)]
  dsimp only [M,Directory.ISA.placementBound,Directory.Layout.candidates] at small
  omega

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1200000 in
/-- Read the actual host address, complete directory dimensions and geometry
control bank from the single combined signed extension on this returning pin.
All 31 ordinary operands and the booked pair/host intervals use the original
native bootstrap and the same live geometry directory. -/
theorem signed_publication_fields {w d : ℕ} (task : SignedTaskArena.Layout) (dir : Directory.Layout)
    (arena : StartupArena) (u : Fin arena.teams) (slot : ℕ) (packet : ReferencePacket w d)
    (other : Arg → Word w) (old : Fin 81 → Word w)
    (origin raw team subtotalWidth fresh reserve gates outputs width off ell extent : ℕ)
    (guess : ℕ → Bool) {f : BroadcastFrame} {advice : AdviceLayout} {hdr : List Bool}
    {z : Bank w} {saved after : Memory w} :
    let B := arena.operands u slot packet
    let args := withDemandBase (task.routeBank arena.frame other) arena.next
    let pub := B.bank (core args origin task.cube.cables task.cube.cells)
    let live := dir.teams*dir.sites
    let controls := controlsBase origin task.cube.cables task.cube.cells dir.entries live
    let addr := bases origin task.cube.cables task.cube.cells dir.entries
    packet.extension = signedProfileExtension task old dir origin task.cube.cables task.cube.cells raw team
      subtotalWidth fresh reserve gates outputs width off ell →
    controls+8 < 2^w → 1<2^w → dir.fields≤2 → task.cube.stop < 2^w →
    Directory.ISA.wordBound (Directory.ISA.placementBound dir addr.privatePairs addr.livePairs extent) < 2^w →
    B.Fits w → ∀ {F : Pins.ProcessorFields B.layout}, JointHeader.BootHeaderState F f advice packet pub hdr z saved →
    (∀ i < arena.next, after i=Pins.preparedMemory B.layout guess saved B.layout.count i) →
    Header arena.frame origin task.cube.cables task.cube.cells dir.entries (readings after) ∧
      readings after (arena.frame+92)=controls ∧ DirectoryHeader dir arena.frame after ∧
      (packet.extension (41 : Fin 81)).val=task.cube.hostDirectory := by
  intro B args pub live controls addr installed ctrl word fields cubeFit room fits F boot resident
  have packed := installed.trans (signedProfileExtension_geometry task old dir origin task.cube.cables
    task.cube.cells raw team subtotalWidth fresh reserve gates outputs width off ell)
  have frame := routing_header arena u slot packet args _ origin task.cube.cables task.cube.cells dir.entries live
    reserve gates outputs width off ell guess fits (by change controls < 2^w; omega) packed boot resident
  obtain ⟨header,ptr,dimensions⟩ := routing_directory _ dir frame
    (publication_dimensions dir addr.privatePairs addr.livePairs extent fields word room)
  refine ⟨header,ptr,dimensions,?_⟩
  rw [installed]
  change task.cube.hostDirectory % 2^w = task.cube.hostDirectory
  apply Nat.mod_eq_of_lt
  have start : task.cube.hostDirectory ≤ task.cube.records := by unfold CubeArena.Layout.records; omega
  have pair : task.cube.records ≤ task.cube.pairBase := by unfold CubeArena.Layout.pairBase TableLayout.reserveEnd; omega
  exact (start.trans (pair.trans (show task.cube.pairBase ≤ task.cube.stop by
    unfold CubeArena.Layout.stop CubeArena.Layout.cellBank; omega))).trans_lt cubeFit

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
