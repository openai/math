import OAI.Computability.VPVNP.PairRefreshTraversalValue
import OAI.Computability.VPVNP.PairSelectedKernelReaders
import OAI.Computability.VPVNP.PairTypedVertexJobs

/-!
# Bits consumed by the selected refresh origin reader

The promoted site's placement fiber has one member. Its actual parser reads the
old outgoing and incoming slots in physical order. The successful local map
contributes an empty choice word, so the node consumes exactly that child packet.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open Compression Compression.Refresh Compression.DegreeRefresh NetworkKernel
open PairSimulation PairSimulation.NodeArguments PairSimulation.LocalHistory RefreshMapOperands

private theorem ofFn_unique {I : Type} {α : Type*} (o : Order I) (one : I) (unique : ∀ i, i = one)
    (f : I → α) : List.ofFn (fun j => f (o.entries j)) = [f one] := by
  let singleton : I ≃ Fin 1 :=
    ⟨fun _ => 0, fun _ => one, fun i => (unique i).symm, fun _ => Subsingleton.elim ..⟩
  have size : o.length = 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (o.entries.trans singleton)
  have same : (fun j => f (o.entries j)) = fun _ => f one := funext fun j => congrArg f (unique _)
  rw [same, List.ofFn_const, size]
  rfl

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {K : Type*} [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f)
  {g : ℕ} (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2^S.portExponent))
  (before : Placed (place X) X.network.Half (promotedSites v))

local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
local notation "site" => promotedSites v
local notation "older" => before (oldSite X v) (old_place X v)
local notation "reader" => originReader B f hf (PassOrigin.refresh X) choice

set_option maxHeartbeats 1800000 in
/-- The actual origin's ordered child list contains the single old-site packet. -/
theorem origin_childPackets (previous : X.network.Site → ℕ) :
    (reader).childPackets previous site before =
      [⟨previous (oldSite X v), packed X (oldSite X v) older⟩] := by
  refine (TermParsers.childPackets_state X reader rfl (fun _ => rfl) (fun _ => rfl) previous site before).trans ?_
  let one : {u : X.network.Site // site = place X u} := ⟨oldSite X v, old_place X v⟩
  have unique (i : {u : X.network.Site // site = place X u}) : i = one :=
    Subtype.ext ((place X).injective (i.property.symm.trans (old_place X v)))
  exact ofFn_unique ((reader).order.children site) one unique
    (fun i => Packet.mk (previous i.val) (packed X i.val (before i.val i.property)))

variable (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh
    S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))
  (witness : ((originReader B f hf (PassOrigin.refresh X) choice).witness (promotedSites v) before new).Choice)

set_option maxHeartbeats 1800000 in
/-- Once a local refresh witness exists, its map requires no additional bits. -/
theorem origin_kernelBits : ((reader).read site before new).encode witness = [] := by
  apply List.length_eq_zero_iff.mp
  exact listedEntryReader_length (f ∘ Sum.inr) _ _
    (refreshNames_spec (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph (Nat.two_pow_pos _) hc
      B.refresh S.port_order hd choice site (splitPlaced X v before) new) witness

/-- The exact bit word consumed by a successful visit to the selected origin. -/
theorem origin_nodeBits : (reader).nodeBits site before new witness = packed X (oldSite X v) older := by
  refine (TermParsers.nodeBits_eq_childPackets (reader) (fun _ => 0) site before new witness).trans ?_
  have bits := congrArg (List.flatMap Packet.bits) (origin_childPackets B f hf X choice v before (fun _ => 0))
  have last := origin_kernelBits B f hf X choice v before new witness
  exact (congrArg₂ List.append bits last).trans (by simp)

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
