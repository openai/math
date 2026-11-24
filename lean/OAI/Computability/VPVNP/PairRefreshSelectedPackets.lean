import OAI.Computability.VPVNP.PairRefreshSelectedParser
import OAI.Computability.VPVNP.PairSelectedPacketOrders

/-! # Typed half-wire packets at selected refresh rows

At a refresh origin the output network of the chosen term is the promoted
state. Reindexing the output half along this equality preserves all packed
bits in their physical order, including independently chosen endpoint values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

set_option maxHeartbeats 1500000
open scoped Fin.CommRing

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords DescriptorSpace TraversalRows TraversalRoles ShrinkRoleDirectory
open DFS NodeArguments VertexImage TreeDecode
open PortRefresh.NewSlots

variable {k : Type} {K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → K} {hf : B.IsSolution f}

private noncomputable abbrev promotedState {v : SelectedLevel B f hf} {u : (v.pass.step.term v.term).output.Site}
    (x : Occurrence v u) :=
  dyadicRefreshNext x.state S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
    B.refresh S.port_order S.degree_bounds.2 x.choice

/-- The selected output half and the native reader's promoted half carry the
same ordered payload. The equivalence also recovers the original term half. -/
noncomputable def halfEquiv (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site)
    (h : tagLevel B f hf v = .refresh) :
    (v.pass.step.term v.term).output.Half u ≃
      (promotedState (occurrence v u h)).network.Half (promotedSites (occurrence v u h).port) := by
  rcases v with ⟨a, g, a', g', X, p, origin, term, tape⟩
  cases origin with
  | shrink => cases h
  | refresh X =>
    rcases u with ⟨⟨base, port⟩, lane⟩
    exact Equiv.refl _

theorem halfEquiv_packed (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site)
    (h : tagLevel B f hf v = .refresh) (z : (v.pass.step.term v.term).output.Half u) :
    pullBits (v.pass.output_eq v.term) (packed (v.pass.next v.term)) u z =
      packed (promotedState (occurrence v u h)) (promotedSites (occurrence v u h).port) (halfEquiv v u h z) := by
  rcases v with ⟨a, g, a', g', X, p, origin, term, tape⟩
  cases origin with
  | shrink => cases h
  | refresh X =>
    rcases u with ⟨⟨base, port⟩, lane⟩
    rfl

variable (n hist w start positions blocks width : ℕ) (leaf : TaggedLayer) (passes : List (SelectedLevel B f hf))
  (room : Rooms n hist w start positions blocks leaf passes)
local notation "base₀" => endAddress (BlockProgram.layout B start positions blocks)
local notation "tags₀" => leaf :: outputTags passes
local notation "R₀" => TerminalLayout.privateRegions (slotDegree S) n ((base₀) + tagWords B.recordLimit (tags₀)) hist
local notation "site₀" => rowSite n hist w start positions blocks width leaf passes room

/-- A stored term-output packet prepares the actual row parser, with its
physical parent and the three private geometry words loaded by the vertex. -/
theorem prepared_at (x : Row passes) (node : BurstRAM.Word w) (s : Scratch w n)
    (z : (passes[x.val.1].pass.step.term passes[x.val.1].term).output.Half x.val.2)
    (atRow : node.val = ShrinkRoleDirectory.address B.recordLimit (base₀) leaf passes x.val)
    (frame : ResidentGeometry s (word ((R₀).histBase + hist)) (word (tagWords B.recordLimit (tags₀) + width))
      (word (R₀).histBase))
    (stored : (Packet.mk (ShrinkRoleDirectory.address B.recordLimit (base₀) leaf passes x.val)
      (pullBits (passes[x.val.1].pass.output_eq passes[x.val.1].term) (packed (passes[x.val.1].pass.next passes[x.val.1].term))
        x.val.2 z)).Stored (R₀).arguments s) : ((site₀) x).Prepared node s := by
  have parent := parent_eq n hist w start positions blocks width leaf passes room x
  have bits := halfEquiv_packed passes[x.val.1] x.val.2 x.property z
  refine ⟨atRow.trans parent.symm, frame, halfEquiv passes[x.val.1] x.val.2 x.property z, ?_⟩
  rw [parent]
  exact bits ▸ stored

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
