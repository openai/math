import OAI.Computability.VPVNP.PairSimulationLeafHandler
import OAI.Computability.VPVNP.PairSimulationLeafAddress
import OAI.Computability.VPVNP.PairSimulationLeafArguments
import OAI.Computability.VPVNP.PairSimulationLeafIncidentLoad
import OAI.Computability.VPVNP.PairPendingArguments

/-!
# Reading a cursor leaf from the physical DFS arguments

The host decodes its current row pointer with the public row stride and
radices. Its private argument arena contains four consecutive bit vectors.
On a stored cursor packet these operations recover the typed position and
all four half-wires, including independently assigned incoming wires.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafHandler

open BurstRAM PrivateRAM CursorRouting CursorNetwork RAMLayout Compression DFS
open LocalHistory TraversalRows NodeArguments
open scoped Fin.CommRing

variable {d W endAddr : ℕ}

/-- Decode the descriptor row using the same operands as the native address reader. -/
def physicalPosition (d : ℕ) [NeZero d] (pub : LeafAddress.Field → Word W)
    (node : Word W) : Position d :=
  let coord := LeafAddress.decode node (pub .base) (pub .stride) (pub .radixB) (pub .radixL)
  (Fin.ofNat d coord.1.val, Fin.ofNat (2^d) coord.2.val)

/-- The four bases passed to the incident-field mover, in native slot order. -/
def portBase (arena : Arena) (node width : ℕ) : LocalPort → ℕ
  | .outgoing side => arena.base node + LeafArguments.portNumber false side * width
  | .incoming side => arena.base node + LeafArguments.portNumber true side * width

/-- Read the single private word occupied by each argument bit. -/
def physicalBuffers (d H w : ℕ) (arena : Arena) (node : Word W)
    (saved : Scratch W endAddr) : Buffers d H w :=
  fun port i => decide ((rawScratch saved ((portBase arena node.val (ramPayloadWidth d H w) port +
    i.val : ℕ) : Word W)).val ≠ 0)

/-- The deterministic prefix supplies its trace and resulting scratch.
The input position and buffer bits are projections of its actual operands. -/
def physicalInput (d e w : ℕ) [NeZero d] (pub : LeafAddress.Field → Word W)
    (arena : Arena) (trace : Word W → Scratch W endAddr → List (Event W))
    (prepared : Word W → Scratch W endAddr → Scratch W endAddr)
    (node : Word W) (saved : Scratch W endAddr) : Input d e w W endAddr :=
  ⟨physicalPosition d pub node, physicalBuffers d (2^e) w arena node saved,
    trace node saved, prepared node saved⟩

variable {b l a p H w : ℕ} [NeZero (b+l)] (hD : 1 < b+l) (hd : 2+p = 2^a)

/-- The pending half-wire packet for this site, with its numerical row address. -/
noncomputable def cursorPacket (node : ℕ) (v : Position (b+l))
    (z : (LeafArguments.state hD hd H w).network.Half (lanePositions (cursorCoordinateLabels b l) v)) :
    Packet :=
  ⟨node, packed (LeafArguments.state hD hd H w) _ z⟩

theorem physicalPosition_eq (pub : LeafAddress.Field → Word W) (node : Word W)
    (cap : ℕ) (v : Position (b+l)) (hwidth : b+l ≤ W)
    (hs : (pub .stride).val = cap+2) (hb : (pub .radixB).val = 2^b)
    (hl : (pub .radixL).val = 2^l)
    (hn : node.val = (sitePointers cap (pub .base).val (siteOrder (LeafArguments.state hD hd H w))
      (lanePositions (cursorCoordinateLabels b l) v)).1) :
    physicalPosition (b+l) pub node = v := by
  obtain ⟨hc, ha⟩ := LeafAddress.decode_leaf_row hD hd (ramFieldBits H w : RAMSystem (b+l) → ℕ)
    cap v node (pub .base) (pub .stride) (pub .radixB) (pub .radixL) hwidth hs hb hl hn
  apply Prod.ext <;> apply Fin.ext
  · change _ % (b+l) = v.1.val
    rw [hc, Nat.mod_eq_of_lt v.1.isLt]
  · change _ % (2^(b+l)) = v.2.val
    rw [ha, Nat.mod_eq_of_lt v.2.isLt]

private theorem storedPort (arena : Arena) (node : Word W) (saved : Scratch W endAddr)
    (v : Position (b+l))
    (z : (LeafArguments.state hD hd H w).network.Half (lanePositions (cursorCoordinateLabels b l) v))
    (fits : (cursorPacket hD hd node.val v z).Fits arena W endAddr)
    (stored : (cursorPacket hD hd node.val v z).Stored arena saved) (dir side : Bool)
    (i : Fin (ramPayloadWidth (b+l) H w)) :
    rawScratch saved ((arena.base node.val + LeafArguments.portNumber dir side *
      ramPayloadWidth (b+l) H w + i.val : ℕ) : Word W) =
      PrivateFields.bitValue W (LeafArguments.buffers hD hd v z (LeafArguments.port dir side) i) := by
  let q := cursorPacket hD hd node.val v z
  let width := ramPayloadWidth (b+l) H w
  have len : q.bits.length = 4 * width := LeafArguments.packed_length_four hD hd _ z
  have hi : LeafArguments.portNumber dir side * width + i.val < q.bits.length := by
    rw [len]
    have lt : i.val < width := i.isLt
    cases dir <;> cases side <;> simp [LeafArguments.portNumber] <;> omega
  let j : Fin q.bits.length := ⟨_, hi⟩
  have hold := stored j
  have write := PrivateFields.storeBits_read (arena.base node.val) q.bits (rawScratch saved) fits.2.2 j
  have physical := LeafArguments.read_port hD hd arena node.val v z (rawScratch saved)
    (len ▸ fits.2.2) dir side i
  change rawScratch saved ((arena.base node.val + LeafArguments.portNumber dir side * width + i.val : ℕ) : Word W) = _
  rw [Nat.add_assoc] at physical ⊢
  exact hold.trans (write.symm.trans physical)

/-- The resident packet satisfies the exact memory precondition of the native
incident-field loader on each of its four ports. -/
theorem physicalStored (arena : Arena) (node : Word W) (saved : Scratch W endAddr)
    (v : Position (b+l))
    (z : (LeafArguments.state hD hd H w).network.Half (lanePositions (cursorCoordinateLabels b l) v))
    (fits : (cursorPacket hD hd node.val v z).Fits arena W endAddr)
    (stored : (cursorPacket hD hd node.val v z).Stored arena saved) :
    LeafIncidentLoad.Stored (portBase arena node.val (ramPayloadWidth (b+l) H w))
      (LeafArguments.buffers hD hd v z) (rawScratch saved) := by
  intro port i
  cases port with
  | outgoing side => exact storedPort hD hd arena node saved v z fits stored false side i
  | incoming side => exact storedPort hD hd arena node saved v z fits stored true side i

/-- Reading the private four-port bank yields the semantic half-wire bits. -/
theorem physicalBuffers_eq (arena : Arena) (node : Word W) (saved : Scratch W endAddr)
    (v : Position (b+l))
    (z : (LeafArguments.state hD hd H w).network.Half (lanePositions (cursorCoordinateLabels b l) v))
    (hW : 0 < W) (fits : (cursorPacket hD hd node.val v z).Fits arena W endAddr)
    (stored : (cursorPacket hD hd node.val v z).Stored arena saved) :
    physicalBuffers (b+l) H w arena node saved = LeafArguments.buffers hD hd v z := by
  funext port i
  have h := physicalStored hD hd arena node saved v z fits stored port i
  change decide ((rawScratch saved (LeafFieldCopy.word W (_ + i.val))).val ≠ 0) = _
  rw [h]
  have one : 1 < 2^W := Nat.one_lt_two_pow hW.ne'
  cases LeafArguments.buffers hD hd v z port i <;>
    simp [PrivateFields.bitValue, Nat.mod_eq_of_lt one]

/-- The physical handler input recovers the semantic cursor site and its
independent buffers on each fitted, stored leaf of the DFS. -/
theorem physicalInput_correct {e : ℕ} (pub : LeafAddress.Field → Word W) (arena : Arena)
    (trace : Word W → Scratch W endAddr → List (Event W))
    (prepared : Word W → Scratch W endAddr → Scratch W endAddr)
    (node : Word W) (saved : Scratch W endAddr) (cap : ℕ) (v : Position (b+l))
    (z : (LeafArguments.state hD hd (2^e) w).network.Half (lanePositions (cursorCoordinateLabels b l) v))
    (hwidth : b+l ≤ W) (hs : (pub .stride).val = cap+2)
    (hb : (pub .radixB).val = 2^b) (hl : (pub .radixL).val = 2^l)
    (hn : node.val = (sitePointers cap (pub .base).val (siteOrder (LeafArguments.state hD hd (2^e) w))
      (lanePositions (cursorCoordinateLabels b l) v)).1)
    (fits : (cursorPacket hD hd node.val v z).Fits arena W endAddr)
    (stored : (cursorPacket hD hd node.val v z).Stored arena saved) :
    physicalInput (b+l) e w pub arena trace prepared node saved =
      ⟨v, LeafArguments.buffers hD hd v z, trace node saved, prepared node saved⟩ := by
  unfold physicalInput
  rw [physicalPosition_eq hD hd pub node cap v hwidth hs hb hl hn,
    physicalBuffers_eq hD hd arena node saved v z (by omega) fits stored]

end PairSimulation.LeafHandler

end VPVNP
end Computability
end OAI
