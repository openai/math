import OAI.Computability.VPVNP.PairSimulationLeafIncidentTable
import OAI.Computability.VPVNP.PairSimulationLeafPhysicalInput
import OAI.Computability.VPVNP.PairSimulationLeafIncidentScratch
import OAI.Computability.VPVNP.PairSimulationLeafArena

/-!
# Supplying the four private half-wire buffers of a DFS node

The parent stores one packed array at the interval indexed by the
descriptor address. The loader reads its four occupied arc slots in
their numerical order. Initializing other stack ports preserves these
cells when the node arena and stack arena are disjoint.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentArena

open BurstRAM PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork RAMLayout
open LeafIncidentLoad (Stored)
open LeafFieldCopy (word)
open scoped Fin.CommRing

variable {W D H w p r k : ℕ}

/-- The four source addresses inside the selected node's private argument packet. -/
def sourceBase (A : NodeArguments.Arena) (node : ℕ) (D H w : ℕ) :=
  LeafIncidentMachine.base (A.base node) (ramPayloadWidth D H w)

theorem sourceBase_eq (A : NodeArguments.Arena) (node D H w : ℕ) :
    sourceBase A node D H w = LeafHandler.portBase A node (ramPayloadWidth D H w) := by
  funext p
  cases p with | outgoing s | incoming s => cases s <;>
    simp [sourceBase,LeafIncidentMachine.base,LeafHandler.portBase,LeafArguments.portNumber]

/-- Scalar stack initialization leaves every independent half-wire bit
available at its original node-arena address. -/
theorem stored_after_scalars {K : Type} (L : StackMachine.Layout K W) (s : RAMTape.Stacks K)
    (A : NodeArguments.Arena) (node : ℕ) (buf : Buffers D H w) (old : Word W → Word W)
    (stored : Stored (sourceBase A node D H w) buf old)
    (fit : A.base node+4*ramPayloadWidth D H w ≤ 2^W)
    (apart : ∀ j, L.base j+(s j).length ≤ A.base node ∨ A.base node+4*ramPayloadWidth D H w ≤ L.base j) :
    Stored (sourceBase A node D H w) buf (LeafLoadedBank.memory L s old) := by
  intro port i
  have h : A.base node ≤ sourceBase A node D H w port ∧
      sourceBase A node D H w port+ramPayloadWidth D H w ≤ A.base node+4*ramPayloadWidth D H w := by
    cases port with
    | outgoing side | incoming side => cases side <;> simp only [sourceBase,LeafIncidentMachine.base] <;> omega
  rw [LeafIncidentBank.memory_outside]
  · exact stored port i
  · intro j
    have hi := i.isLt
    have hsep := apart j
    change (_ % 2^W) < _ ∨ _ ≤ (_ % 2^W)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- A stored packet read from DFS scratch remains valid in the represented
scalar bank that immediately precedes the incident copy. -/
theorem stored_leaf {K : Type} {b l a z endAddr : ℕ} [NeZero (b+l)] (hd : 1 < b+l) (hz : 2+z = 2^a)
    (A : NodeArguments.Arena) (node : Word W) (v : Position (b+l))
    (halves : (LeafArguments.state hd hz H w).network.Half
      (lanePositions (cursorCoordinateLabels b l) v))
    (L : StackMachine.Layout K W) (s : RAMTape.Stacks K) (old : Word W → Word W)
    (fits : (LeafHandler.cursorPacket hd hz node.val v halves).Fits A W endAddr)
    (stored : (LeafHandler.cursorPacket hd hz node.val v halves).Stored A (DFS.scratch endAddr old))
    (apart : ∀ j, L.base j+(s j).length ≤ A.base node.val ∨
      A.base node.val+4*ramPayloadWidth (b+l) H w ≤ L.base j) :
    Stored (sourceBase A node.val (b+l) H w) (LeafArguments.buffers hd hz v halves) (LeafLoadedBank.memory L s old) := by
  have len := LeafArguments.packed_length_four hd hz _ halves
  have fit : A.base node.val+4*ramPayloadWidth (b+l) H w ≤ 2^W := len ▸ fits.2.2
  apply stored_after_scalars _ _ _ _ _ _ _ fit apart
  have h := LeafHandler.physicalStored hd hz A node (DFS.scratch endAddr old) v halves fits stored
  rw [← sourceBase_eq] at h
  intro port i
  have hh := h port i
  have bound : A.base node.val ≤ sourceBase A node.val (b+l) H w port ∧
      sourceBase A node.val (b+l) H w port+ramPayloadWidth (b+l) H w ≤ A.base node.val+4*ramPayloadWidth (b+l) H w := by
    cases port with | outgoing side | incoming side => cases side <;> simp only [sourceBase,LeafIncidentMachine.base] <;> omega
  have above : endAddr ≤ A.base node.val := fits.1
  have hi := i.isLt
  have ha : endAddr ≤ (word W (sourceBase A node.val (b+l) H w port+i.val)).val := by
    change _ ≤ _ % _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simpa only [NodeArguments.rawScratch,ha,↓reduceDIte,DFS.scratch] using hh

/-- In the physical regions of a leaf the whole argument packet precedes
every stack, so its bits survive scalar initialization without a per-port
separation hypothesis. -/
theorem stored_leaf_regions {K : Type} {b l a z endAddr ports : ℕ} [NeZero (b+l)]
    (hd : 1 < b+l) (hz : 2+z = 2^a) (R : LeafArena.Regions) (node : Word W)
    (v : Position (b+l)) (halves : (LeafArguments.state hd hz H w).network.Half
      (lanePositions (cursorCoordinateLabels b l) v))
    (order : K ↪ Fin ports) (capacity : ℕ) (room : R.stackBase + ports*capacity < 2^W)
    (s : RAMTape.Stacks K) (old : Word W → Word W) (active : node.val < R.nodes)
    (fits : (LeafHandler.cursorPacket hd hz node.val v halves).Fits R.arguments W endAddr)
    (stored : (LeafHandler.cursorPacket hd hz node.val v halves).Stored R.arguments (DFS.scratch endAddr old)) :
    Stored (sourceBase R.arguments node.val (b+l) H w) (LeafArguments.buffers hd hz v halves)
      (LeafLoadedBank.memory (R.layout order capacity room) s old) := by
  apply stored_leaf hd hz R.arguments node v halves _ s old fits stored
  intro j
  apply Or.inr
  have size : 4*ramPayloadWidth (b+l) H w ≤ R.arguments.stride :=
    (LeafArguments.packed_length_four hd hz _ halves) ▸ fits.2.1
  have before := R.node_before active
  have after := R.stack_above order capacity room j
  have interval : R.histBase ≤ R.stackBase := by
    unfold LeafArena.Regions.stackBase LeafArena.Regions.cacheBase
    omega
  omega

end PairSimulation.LeafIncidentArena

end VPVNP
end Computability
end OAI
