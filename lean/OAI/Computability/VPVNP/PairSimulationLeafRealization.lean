import OAI.Computability.VPVNP.PairSimulationLeafFrame
import OAI.Computability.VPVNP.PairSimulationLeafJobReadback

/-! # Physical realization of each actual compressed cursor-leaf occurrence -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafHandler

open BurstRAM PrivateRAM CursorRouting CursorNetwork LeafStartup StackMachine DFS
open LocalHistory NodeArguments
open scoped Fin.CommRing

variable {e w W endAddr : ℕ}
  {L : PrimedInputRAM.Lengths} {n ai H s : ℕ} {Q : PrimedInputRAM.Layout L n ai H w}
  (D : PrimedCounter.Data Q s) (hw : 2 ≤ w)
  (storage : StackMachine.Layout (Port 52 34) W) (clock : ℕ)
  (node : Word W) (saved : Scratch W endAddr)

section Cursor

open RAMLayout Compression TraversalRows

variable {b l a p : ℕ} [NeZero (b+l)] (hD : 1 < b+l) (hd : 2+p = 2^a)
    {R : Type*} [CommRing R] {Label : Type} [Fintype Label] (f : Label → R)
    (hc' : 2^(b+l)*2^e < 2^w) (bound : NominationClock D hw hc' clock)
    (pub : LeafAddress.Field → Word W) (arena : Arena)
    (trace : Word W → Scratch W endAddr → List (Event W))
    (prepared : Word W → Scratch W endAddr → Scratch W endAddr)
    (cap : ℕ) (v : Position (b+l))
    (z : (LeafArguments.state hD hd (2^e) w).network.Half (lanePositions (cursorCoordinateLabels b l) v))
    (row : StoredCursorRow hD hd pub arena node saved cap v z)

include row in
/-- The true selected leaf job has the correct descriptor address and event
choices. Every designated private histogram word retains its old value.
This includes repeated visits with a nonzero preexisting histogram. -/
theorem cursorHook_realizes
    (cell : Label → {a : Word W // endAddr ≤ a.val})
    (away : ∀ label j, (cell label).val.val < storage.base j ∨
      storage.base j+storage.capacity ≤ (cell label).val.val)
    (det : choiceBits (trace node saved) = [])
    (prefixFrame : ∀ label, prepared node saved (cell label) = saved (cell label))
    (room : ∀ j, (auxiliaryBank D hw hc' v (LeafArguments.buffers hD hd v z) j).length+clock ≤ storage.capacity) :
    ∀ (code suffix : List Bool),
      (∃ x, code = (cursorSiteReader hD hd D hw hc' f clock bound v z).encode x) →
      ∃ actual, (cursorHook D hw hc' clock storage pub arena trace prepared).read node saved
        (code++suffix) = some (actual,suffix) ∧ actual.enabled saved ∧
        RealizesJob (fun old label => (old (cell label)).val) ⟨node.val,code,fun _ => 0⟩ actual := by
  intro code suffix chosen
  obtain ⟨x,hx⟩ := chosen
  obtain ⟨actual,hit⟩ := (cursorHook_read_iff hD hd D hw hc' f clock bound storage pub arena trace
    prepared node saved cap v z row (code++suffix) suffix).mpr ⟨x,congrArg (· ++ suffix) hx⟩
  let input := physicalInput (b+l) e w pub arena trace prepared
  have hp := physicalPosition_eq (H := 2^e) (w := w) hD hd pub node cap v row.width row.stride
    row.radixB row.radixL row.address
  have hb := physicalBuffers_eq hD hd arena node saved v z (by have := row.width; omega) row.fit row.stored
  have capacity (j : Port 52 34) :
      (auxiliaryBank D hw hc' (input node saved).pos (input node saved).buffers j).length+clock ≤ storage.capacity := by
    change (auxiliaryBank D hw hc' (physicalPosition (b+l) pub node) (physicalBuffers (b+l) (2^e) w arena node saved) j).length+clock ≤ _
    rw [hp,hb]
    exact room j
  obtain ⟨addr,enabled,consumed,frame⟩ := parser_observations D hw hc' storage input clock node saved
    (code++suffix) suffix actual hit det capacity
  refine ⟨actual,hit,(enabled saved).mpr rfl,⟨?_,(List.append_cancel_right consumed).symm,?_⟩⟩
  · change actual.node = (node.val : Word W)
    simp [addr]
  · intro old h label
    have eqn := (enabled old).mp h
    subst old
    change (actual.update saved (cell label)).val = (saved (cell label)).val + 0
    rw [frame (cell label) (away label), show (input node saved).prepared (cell label) = _ from prefixFrame label,
      Nat.add_zero]

end Cursor
end PairSimulation.LeafHandler

end VPVNP
end Computability
end OAI
