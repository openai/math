import OAI.Computability.VPVNP.PairTreePacketLayers
import OAI.Computability.VPVNP.PairTraversalSelectedOrder

/-!
# The actual ordered half-wire packet at every selected pass

The next term's numerical slot order agrees with the state's argument
arena, also across the output network identification between two stages.
At the initial cursor site this recovers the four independently supplied
port buffers used by the physical leaf.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NetworkKernel CompressorRecords LocalHistory NodeArguments Compression
open scoped Fin.CommRing
open private castParsers from OAI.Computability.VPVNP.PairSimulationAssemblyBounds

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R}
    {a g a' g' b n : ℕ} {X : State a g}

/-- Numerical packets at the input to any suffix of the actual schedule. -/
theorem execution_inputPacked (E : StateExecution R b n X) (W : E.MapWitnesses f)
    (r : ExecutionReaders E W) (rec : E.Records) (z : E.Choices) (ordered : ExecutionOrders E W r)
    (ptr : RowPointers (E.termChain rec z)) (addr : X.network.Site → ℕ) (v : X.network.Site)
    (h : X.network.Half v) :
    (fromRows (E.termChain rec z) (branchParsers E W r rec z) ptr addr (packed (E.finalState z))).1 v h =
      ⟨addr v,packed X v h⟩ := by
  cases E with
  | done => rfl
  | more p tail =>
    change Packet.mk (addr v) ((r.1.termParsers z.1).halfBits v h) = _
    have out := ordered.1.2.1 z.1 v
    have inc := ordered.1.2.2 z.1 v
    change (r.1.termParsers z.1).order.outgoing v = outgoingOrder _ v at out
    change (r.1.termParsers z.1).order.incoming v = incomingOrder _ v at inc
    rw [TermParsers.halfBits,out,inc,packed_eq_encode]
    rfl

/-- Pull a site's half-wire encoder back across a network equality so that the output term can
use the next state's packed bits. -/
def pullBits {N Y : Network} (eqn : N = Y) (bits : ∀ v, Y.Half v → List Bool) :
    ∀ v, N.Half v → List Bool := by cases eqn; exact bits

private theorem castInputPacked {N Z Y : Network} (eqn : N = Z) (c : TermChain R Z Y)
    (r : ChainParsers f c) (finalBits : ∀ v, Y.Half v → List Bool)
    (before : ∀ v, Z.Half v → List Bool)
    (input : ∀ ptr addr v h, (fromRows c r ptr addr finalBits).1 v h = ⟨addr v,before v h⟩)
    (ptr : RowPointers (eqn.symm ▸ c : TermChain R N Y)) (addr : N.Site → ℕ) (v : N.Site) (h : N.Half v) :
    (fromRows (eqn.symm ▸ c : TermChain R N Y) (castParsers eqn.symm c r) ptr addr finalBits).1 v h =
      ⟨addr v,pullBits eqn before v h⟩ := by cases eqn; exact input ptr addr v h

/-- The output arguments consumed by the shrink/refresh kernel at this
level are precisely the actual packed half-wires of its selected next state. -/
theorem execution_outputPacked (p : StatePass R X a' g') (tail : ∀ i, StateExecution R b n (p.next i))
    (W : (StateExecution.more p tail).MapWitnesses f) (r : ExecutionReaders (.more p tail) W)
    (rec : (StateExecution.more p tail).Records) (z : (StateExecution.more p tail).Choices)
    (ordered : ExecutionOrders (.more p tail) W r)
    (ptr : RowPointers ((StateExecution.more p tail).termChain rec z)) (addr : X.network.Site → ℕ)
    (v : (p.step.term z.1).output.Site) (h : (p.step.term z.1).output.Half v) :
    (fromRows ((StateExecution.more p tail).termChain rec z) (branchParsers (.more p tail) W r rec z)
      ptr addr (packed ((StateExecution.more p tail).finalState z))).2.1 v h =
        ⟨(ptr.1 v).1,pullBits (p.output_eq z.1) (packed (p.next z.1)) v h⟩ := by
  let E := tail z.1
  let rr := r.2 z.1
  let records := rec.2 z.1
  exact castInputPacked (p.output_eq z.1) (E.termChain records z.2) (branchParsers E (W.2 z.1) rr records z.2)
    (packed (E.finalState z.2)) (packed (p.next z.1))
    (execution_inputPacked E (W.2 z.1) rr records z.2 (ordered.2 z.1)) ptr.2 (fun u => (ptr.1 u).1) v h

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (κ : B.Entry → R) (hκ : B.IsSolution κ)

/-- In particular the very first packet for the routed RAM cursor has the
actual cursor state's packed bits and its actual leaf-row pointer. -/
theorem selected_inputPacked {n : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute κ hκ T hT X).Choices) :
    let E := B.execute κ hκ T hT X
    let c := E.termChain (B.records κ hκ T hT X) z
    let r := selectedParsers B κ hκ T hT X z
    ∀ ptr addr v h, (fromRows c r ptr addr (packed (E.finalState z))).1 v h = ⟨addr v,packed X v h⟩ := by
  intro E c r
  exact execution_inputPacked E _ _ _ z (execute_readerOrders B κ hκ T hT X)

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
