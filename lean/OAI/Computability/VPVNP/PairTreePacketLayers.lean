import OAI.Computability.VPVNP.PairTreeDecodeDomain

/-! # Canonical ordered packets of all layers of the selected compression -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NetworkKernel CompressorRecords LocalHistory NodeArguments
open Compression
open scoped Fin.CommRing

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R} {N Y : Network}

/-- A nonterminal layer uses the half-wire layout of the next real term.
The final layer uses the endpoint collector's root half-wire layout. -/
noncomputable def fromRows {N Y : Network} (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (addr : N.Site → ℕ) (finalBits : ∀ v, Y.Half v → List Bool) : Packets N × PacketLayers c :=
  match c with
  | .done _ => (fun v z => ⟨addr v,finalBits v z⟩,PUnit.unit)
  | .more _ _ tail =>
    let later := fromRows tail r.2 ptr.2 (fun v => (ptr.1 v).1) finalBits
    (fun u z => ⟨addr u,r.1.halfBits u z⟩,(later.1,later.2))

theorem fromRows_inputAddress (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (addr : N.Site → ℕ) (finalBits : ∀ v, Y.Half v → List Bool) (u : N.Site) (z : N.Half u) :
    ((fromRows c r ptr addr finalBits).1 u z).node = addr u := by cases c <;> rfl

theorem fromRows_pointers (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (addr : N.Site → ℕ) (finalBits : ∀ v, Y.Half v → List Bool) :
    PointerLayers c ptr (fromRows c r ptr addr finalBits).2 := by
  induction c with
  | done => trivial
  | more t rec tail ih =>
    exact ⟨fromRows_inputAddress tail r.2 ptr.2 (fun v => (ptr.1 v).1) finalBits,
      ih r.2 ptr.2 (fun v => (ptr.1 v).1) finalBits⟩

/-- At the singleton final root this gives the exact packet prepared by
the external endpoint gather, independent of the branch's depth. -/
theorem fromRows_final (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (addr : N.Site → ℕ) (finalBits : ∀ v, Y.Half v → List Bool) :
    finalPackets c (fromRows c r ptr addr finalBits).2 (fromRows c r ptr addr finalBits).1 =
      fun v z => ⟨lastRowAddresses c ptr addr v,finalBits v z⟩ := by
  induction c with
  | done => rfl
  | more t rec tail ih => exact ih r.2 ptr.2 (fun v => (ptr.1 v).1) finalBits

/-- The list of half-wire buffers used by the local row is exactly
the list prepared by its physical child-field pass. -/
theorem fromRows_children {t : Term R N} {rec : t.output.Site → SiteRecords} (tail : TermChain R t.output Y)
    (r : ChainParsers f (.more t rec tail)) (ptr : RowPointers (.more t rec tail))
    (addr : N.Site → ℕ) (finalBits : ∀ v, Y.Half v → List Bool) (v : t.output.Site)
    (a : Placed t.place N.Half v) :
    children r.1 (fromRows (.more t rec tail) r ptr addr finalBits).1 v a =
      r.1.childPackets addr v a := rfl

/-- On a real state the incoming layer of the pass is in the arena's exact
outgoing-then-incoming slot layout. -/
theorem fromRows_packed {degree lanes : ℕ} (X : State degree lanes) {t : Term R X.network}
    {rec : t.output.Site → SiteRecords} (tail : TermChain R t.output Y) (r : ChainParsers f (.more t rec tail))
    (ptr : RowPointers (.more t rec tail)) (addr : X.network.Site → ℕ)
    (finalBits : ∀ v, Y.Half v → List Bool) (hp : r.1.payload = statePayload X)
    (ho : ∀ u, r.1.order.outgoing u = outgoingOrder X u)
    (hi : ∀ u, r.1.order.incoming u = incomingOrder X u)
    (u : X.network.Site) (z : X.network.Half u) :
    (fromRows (.more t rec tail) r ptr addr finalBits).1 u z = ⟨addr u, packed X u z⟩ := by
  change Packet.mk (addr u) (r.1.halfBits u z) = _
  simp [TermParsers.halfBits,hp,ho,hi,packed_eq_encode]

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
