import OAI.Computability.VPVNP.PairSimulationLeafIncidentMachine
import OAI.Computability.VPVNP.PairSimulationLeafIncidentBank

/-!
# Native incident loader at the auxiliary stack-interpreter boundary

The executable two-direction successor scan and triangular layer scan finish
with the exact auxiliary stack bank. Its scalar cells and pending descriptor
stack survive the copy. The new DFS scratch is determined on all addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentBank

open BurstRAM PrivateRAM CursorNetwork CursorRouting RAMLayout RAMTape StackMachine
open PrimedCounter.GuessWord LeafStartup

set_option synthInstance.maxSize 10000

variable {d e w W p r k endAddr top : ℕ} [NeZero d]
variable {A : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout A n a H w}

/-- The destination stack port for incident bits in the auxiliary validator with 52 registers
and 34 public operands. -/
abbrev incident := LeafLoadedBank.incidentPort 52 34

/-- Execute the actual leaf incident table from the six raw geometry words.
The stack-top register is shared with its virtual port, and the protected
register assignment is disjoint from the table's explicitly changed rows. -/
theorem machine_run (data : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hcap : 2^d*2^e < 2^w)
    (v : Site d) (buf : Buffers d (2^e) w) (L : Layout (Port 52 34) W)
    (stack : Register (Port 52 34) ↪ Fin r) (geom : Fin 30 ↪ Fin r)
    (pc : LeafIncidentMachine.Stage → Fin p) (M : Machine W p r k) (done : Fin p)
    (linked : LeafIncidentMachine.Linked M pc geom done) (node : ℕ) (c : Config W p r)
    (entry : c.pc = pc (.inl 0))
    (ready : LeafIncidentGeometry.Ready d (2^e) w v.val node (L.base incident) (c.reg ∘ geom))
    (hDW : d < W)
    (stored : LeafIncidentLoad.Stored (LeafIncidentMachine.base node (ramPayloadWidth d (2^e) w))
      buf c.privateMem)
    (srcFits : node+4*ramPayloadWidth d (2^e) w ≤ 2^W)
    (sep : node+4*ramPayloadWidth d (2^e) w ≤ L.base incident ∨
      L.base incident+width d (2^e) w ≤ node)
    (shared : geom 24 = stack (.top incident))
    (protect : ∀ j : Register (Port 52 34), j ≠ .tmp → j ≠ .top incident →
      ∀ i ∈ LeafIncidentMachine.changed, stack j ≠ geom i)
    (old : Word W → Word W) (pending : List (Word W)) (htop : top+pending.length = endAddr)
    (previous : DFS.Represents old top pending) (above : ∀ j, endAddr ≤ L.base j) :
    let x := auxiliary data hw hcap (0,v) buf
    let scalar := LeafRegisterBank.scalarBank (field (r := 52)) x data.pub
    let full := bank 52 x data.pub
    Represents L stack c scalar → (∀ j, (scalar j).length ≤ L.capacity) →
    width d (2^e) w ≤ L.capacity → c.privateMem = LeafLoadedBank.memory L scalar old →
    ∃ out, Prefix M c (List.replicate (LeafIncidentMachine.ticks v (2^e) w) .tick) out ∧
      LeafIncidentMachine.Result geom done (L.base incident) v buf c out ∧
      Represents L stack out full ∧ out.privateMem = LeafLoadedBank.memory L full old ∧
      DFS.Represents out.privateMem top pending ∧
      DFS.scratch endAddr out.privateMem = LeafLoadedBank.scratch L full (DFS.scratch endAddr old) := by
  intro x scalar full rep fit room initial
  have dest := (Nat.add_le_add_left room (L.base incident)).trans_lt (L.fits incident)
  obtain ⟨_, out, prefixRun, phys⟩ := LeafIncidentMachine.run M pc geom done linked node (L.base incident)
    buf v c entry ready hDW stored dest srcFits sep
  have mem : out.privateMem = LeafFieldCopy.place (L.base incident)
      (List.ofFn (incidentBits x.sends x.v)) c.privateMem := by
    have eqn := sends_incident (0,v) buf
    change incidentBits x.sends x.v = incidentBuffer (0,v) buf at eqn
    rw [eqn]
    exact phys.memory
  have newTop : out.reg (stack (.top incident)) = L.address incident (width d (2^e) w) := by
    rw [← shared]
    exact phys.top
  obtain ⟨rep', exactMem⟩ := fullBank L stack x data.pub c out rep fit room mem newTop
    (fun j ht hi => phys.frame _ (protect j ht hi)) old initial
  exact ⟨out, prefixRun, phys, rep', exactMem, initialized_scratch L full exactMem above htop previous⟩

end PairSimulation.LeafIncidentBank

end VPVNP
end Computability
end OAI
