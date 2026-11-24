import OAI.Computability.VPVNP.PairSelectedPacketOrders
import OAI.Computability.VPVNP.PairTreeEmissions

/-!
# Joining the native shrink and refresh row checks along a selected branch

Each local implementation sees the two actual compressor states on either
side of its own pass, in their numerical slot order. Transport across the
output-network equality and recursion through the selected passes provide
both the decoder and emission contracts for the final term chain.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NetworkKernel CompressorRecords LocalHistory NodeArguments Compression
open scoped Fin.CommRing
open private castParsers from OAI.Computability.VPVNP.PairSimulationAssemblyBounds

variable {W endAddr : ℕ} {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R}
    (hook : HookParser W endAddr) (valid : List Packet → Scratch W endAddr → Prop)
    (hist : Scratch W endAddr → L → ℕ) (guard : VisitPath W endAddr → Prop)

/-- Return a row-pointer family for the original term chain by undoing the transport of its
input network. -/
def uncastPointers {N Z Y : Network} (e : N = Z) (c : TermChain R Z Y)
    (ptr : RowPointers (e.symm ▸ c : TermChain R N Y)) : RowPointers c := by cases e; exact ptr

/-- Transport a numerical site-address function from the term's output network to the equal
network of the following state. -/
def pushAddress {N Z : Network} (e : N = Z) (addr : N.Site → ℕ) : Z.Site → ℕ := by cases e; exact addr

private def Claims {N Y : Network} (c : TermChain R N Y) (r : ChainParsers f c)
    (ptr : RowPointers c) (addr : N.Site → ℕ) (bits : ∀ v, Y.Half v → List Bool) : Prop :=
  let frames := fromRows c r ptr addr bits
  StepLayers hook valid c r ptr frames.2 frames.1 ∧ EmissionLayers valid hist guard c r ptr frames.2 frames.1

private theorem castClaims {N Z Y : Network} (e : N = Z) (c : TermChain R Z Y) (r : ChainParsers f c)
    (ptr : RowPointers (e.symm ▸ c : TermChain R N Y)) (addr : N.Site → ℕ) (bits : ∀ v, Y.Half v → List Bool)
    (h : Claims hook valid hist guard c r (uncastPointers e c ptr) (pushAddress e addr) bits) :
    Claims hook valid hist guard (e.symm ▸ c : TermChain R N Y) (castParsers e.symm c r) ptr addr bits := by
  cases e; exact h

/-- Both local obligations at a state pass, with the actual half-wire
packets in its source and successor states. -/
def PassChecks {a g b n : ℕ} {X : State a g} (p : StatePass R X b n) {K : p.MapWitnesses f}
    (r : PassReaders p K) (i : p.step.Choice) (ptr : (p.step.term i).output.Site → ℕ × ℕ)
    (addr : X.network.Site → ℕ) : Prop :=
  let before := fun v z => Packet.mk (addr v) (packed X v z)
  let next := fun v z => Packet.mk (ptr v).1 (pullBits (p.output_eq i) (packed (p.next i)) v z)
  NodeStep hook valid (r.termParsers i) ptr before next ∧ EmitsNode valid hist guard (r.termParsers i) ptr before next

/-- A sequence of checks for the individually selected native shrinking
and degree-refresh rows. -/
def ExecutionChecks {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (K : E.MapWitnesses f) (r : ExecutionReaders E K) (rec : E.Records) (z : E.Choices)
    (ptr : RowPointers (E.termChain rec z)) (addr : X.network.Site → ℕ) : Prop :=
  match E with
  | .done _ => True
  | .more p tail =>
    PassChecks hook valid hist guard p r.1 z.1 ptr.1 addr ∧
      ExecutionChecks (tail z.1) (K.2 z.1) (r.2 z.1) (rec.2 z.1) z.2
        (uncastPointers (p.output_eq z.1) _ ptr.2) (pushAddress (p.output_eq z.1) (fun v => (ptr.1 v).1))

/-- A local proof over the actual state records of each pass supplies the
complete selected-branch hypotheses used by the terminal vertex worker. -/
theorem execution_checks {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (K : E.MapWitnesses f) (r : ExecutionReaders E K) (rec : E.Records) (z : E.Choices)
    (ptr : RowPointers (E.termChain rec z)) (addr : X.network.Site → ℕ) (orders : ExecutionOrders E K r)
    (checked : ExecutionChecks hook valid hist guard E K r rec z ptr addr) :
    let c := E.termChain rec z
    let readers := branchParsers E K r rec z
    let frames := fromRows c readers ptr addr (packed (E.finalState z))
    StepLayers hook valid c readers ptr frames.2 frames.1 ∧ EmissionLayers valid hist guard c readers ptr frames.2 frames.1 := by
  change Claims hook valid hist guard _ _ _ _ _
  induction E with
  | done => exact ⟨trivial,trivial⟩
  | @more a g a' g' X p tail ih =>
    let exec := StateExecution.more p tail
    let d := (tail z.1).termChain (rec.2 z.1) z.2
    let pars := branchParsers (tail z.1) (K.2 z.1) (r.2 z.1) (rec.2 z.1) z.2
    let frames := fromRows (exec.termChain rec z) (branchParsers exec K r rec z) ptr addr (packed (exec.finalState z))
    let before := fun v z => Packet.mk (addr v) (packed X v z)
    let next := fun v y => Packet.mk (ptr.1 v).1 (pullBits (p.output_eq z.1) (packed (p.next z.1)) v y)
    have oldEq : frames.1 = before := by
      funext v y
      exact execution_inputPacked exec K r rec z orders ptr addr v y
    have newEq : frames.2.1 = next := by
      funext v y
      exact execution_outputPacked p tail K r rec z orders ptr addr v y
    have first : NodeStep hook valid (r.1.termParsers z.1) ptr.1 frames.1 frames.2.1 ∧
        EmitsNode valid hist guard (r.1.termParsers z.1) ptr.1 frames.1 frames.2.1 := by
      rw [oldEq,newEq]; exact checked.1
    have tailProof := ih z.1 (K.2 z.1) (r.2 z.1) (rec.2 z.1) z.2
      (uncastPointers (p.output_eq z.1) d ptr.2) (pushAddress (p.output_eq z.1) (fun v => (ptr.1 v).1))
      (orders.2 z.1) checked.2
    have later := castClaims hook valid hist guard (p.output_eq z.1) d pars ptr.2 (fun v => (ptr.1 v).1)
      (packed (exec.finalState z)) tailProof
    exact ⟨⟨first.1,later.1⟩,⟨first.2,later.2⟩⟩

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
