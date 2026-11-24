import OAI.Computability.VPVNP.PairRefreshOriginLevelRead
import OAI.Computability.VPVNP.PairRefreshOriginLevelGeometry
import OAI.Computability.VPVNP.PairRefreshHookEmission

/-! # Histogram and frontier effects of the selected refresh occurrence -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace PortRefresh
open PortRefresh.NewSlots
open TraversalRows TraversalRoles LocalHistory NetworkKernel NodeArguments TreeDecode
open VertexImage DFS
open scoped Fin.CommRing

set_option quotPrecheck false

attribute [local irreducible] executeLevels originReader selectedDesc siteOrder packed children
  layerBase choiceEquiv placedEquiv halfEquiv

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f)
    {lanes : ℕ} (blocks : ℕ) (budget : blocks * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (branch : (B.execute f hf blocks budget X).Choices)
    (n hist w start positions width : ℕ)

local notation "passes" => executeLevels B f hf blocks budget X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "first" => endAddress (BlockProgram.layout B start positions blocks)
local notation "tags₀" => selected B f hf blocks budget X branch
local notation "pos" => layerBase B.recordLimit first (tags₀)
local notation "format₀" => SelectedPacketFormat B f hf blocks budget X branch first
local notation "desc₀" => selectedDesc B f hf blocks budget X branch first
variable (room : Rooms n hist w start positions blocks ⟨leafLayer (siteOrder X), .cursor⟩
    (executeLevels B f hf blocks budget X branch))
    (order : B.Entry ≃ Fin hist) (pub : Fin 11 → Word w) (m : Memory w) (x : Row
      (executeLevels B f hf blocks budget X branch))
local notation "u₀" => x.val.2
local notation "v₀" => (passes).get x.val.1
local notation "R₀" => rowSite n hist w start positions blocks width (leaf₀) passes room x
local notation "r₀" => originReader B f hf (v₀).origin (v₀).term
local notation "ties₀" => RefreshBlockPlan.order B
local notation "stride₀" => LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)
local notation "nextBase" => TraversalRows.address B.recordLimit ((pos) x.val.1.val)
  (siteOrder (v₀).input).length
local notation "ptr" => sitePointers B.recordLimit nextBase (ShrinkRoleDirectory.outputOrder (v₀))
local notation "src" => (fun u z => Packet.mk (sitePointers B.recordLimit ((pos) x.val.1.val)
  (siteOrder (v₀).input) u).1 (packed (v₀).input u z))
local notation "head₀" => (fun z => Packet.mk ((ptr) u₀).1
  (pullBits ((v₀).pass.output_eq (v₀).term) (packed ((v₀).pass.next (v₀).term)) u₀ z))
local notation "newHalf" => halfEquiv (v₀) u₀ x.property
local notation "counts" => privateHistogram order.symm (R₀).regions.histBase
variable (data : Fin 10 → Word w) (vals : LeafSourceLoad.Static 34 → Word w) (nodeCap limit : ℕ)
local notation "valid" => Budgeted (R₀).arena (format₀) (VertexFrameData (R₀).regions data
  (R₀).roleOffset vals)
  (desc₀) (counts) nodeCap limit

set_option maxHeartbeats 2000000 in
-- Transport the dependent occurrence and its ordered packet through the port equivalence.
/-- The exact selected term supplies the code and every exponent increment
of this body. Its update prepares the ordered old packets for DFS. -/
theorem selected_effect (z : ((v₀).pass.step.term (v₀).term).output.Half u₀)
    (a : Placed ((v₀).pass.step.term (v₀).term).place (v₀).input.network.Half u₀)
    (c : ((r₀).witness u₀ a z).Choice) (pending : List Packet) (s : Scratch w n)
    (ready : valid ((head₀) z :: pending) s) (hw : 0 < w)
    (positive : 0 < (R₀).oldNode) (cacheFit : (R₀).regions.cacheBase + 38 ≤ 2 ^ w)
    (limitFit : limit < 2 ^ w) (capFit : n ≤ nodeCap) (tail : List Bool) (body : VisitPath w n)
    (read : ((R₀).hook (ties₀) (stride₀) order pub m).read (word (R₀).parent) s
      ((r₀).nodeBits u₀ a z c ++ tail) = some (body, tail)) :
    RealizesJob (counts) ⟨((ptr) u₀).1, (r₀).nodeBits u₀ a z c, ((r₀).witness u₀ a
      z).exponents c⟩ body ∧
      body.enabled s ∧ valid (children (r₀) (src) u₀ a ++ pending) (body.update s) := by
  let R := R₀
  let pe := placedEquiv (v₀) u₀ x.property
  let new := (newHalf) z
  let occ := choiceEquiv (v₀) u₀ x.property z ⟨a, c⟩
  let child := fun old : Placed (TraversalPlan.place R.state) R.state.network.Half R.newerSite =>
    RefreshHook.packet R.state R.olderSite R.oldNode
    (old R.olderSite (TraversalPlan.old_place R.state R.port))
  have onlyChild old : children (r₀) (src) u₀ old = [child (pe old)] :=
    children_eq (v₀) u₀ x.property old ((pos) x.val.1.val)
  have single old : children (r₀) (src) u₀ (pe.symm old) = [child old] :=
    (onlyChild (pe.symm old)).trans (congrArg (fun b => [child b]) (pe.apply_symm_apply old))
  have shape old : (desc₀) R.parent = subtreeAddresses (desc₀) (child old) := by
    have h := level_children_shape B f hf blocks budget X branch n hist w start positions
      width room x (pe.symm old)
    exact h.trans ((congrArg (List.flatMap (subtreeAddresses desc₀)) (single old)).trans
      (List.append_nil _))
  have typed old : (format₀) (child old) :=
    level_children_format B f hf blocks budget X branch start positions x (pe.symm old)
      ((congrArg (fun ls => child old ∈ ls) (single old)).mpr List.mem_cons_self)
  have eqn := choice_fields (v₀) u₀ x.property z a c
  have hp := level_parent B f hf blocks budget X branch n hist w start positions width room x
  have packetEq := level_packet B f hf blocks budget X branch n hist w start positions width
    room x z
  have prepared := (congrArg (fun q : Packet => valid (q :: pending) s) packetEq).mp ready
  have nativeRead := (congrArg (fun bs => (R.hook (ties₀) (stride₀) order pub m).read (word
    R.parent) s
    (bs ++ tail) = some (body, tail)) eqn.2.1).mp read
  have eff := R.origin_effect (ties₀) (stride₀) order pub m f hf new data R.roleOffset vals
    (format₀) (desc₀) nodeCap limit pending s prepared hw shape typed
    (level_node_lt B f hf blocks budget X branch n hist w start positions width room x)
    positive cacheFit limitFit capFit occ.1 occ.2 tail body nativeRead
  have after := (onlyChild a).trans (congrArg (fun b => [child b]) eqn.1.symm)
  refine ⟨⟨eff.1.address.trans (congrArg (fun j : ℕ => (j : Word w)) hp.symm),
    eff.1.bits.trans eqn.2.1.symm, ?_⟩, eff.2.1, ?_⟩
  · intro q h label
    exact (eff.1.counts q h label).trans (congrArg (counts q label + ·) (congrFun eqn.2.2.symm
      label))
  · exact (congrArg (fun children => valid (children ++ pending) (body.update s)) after).mpr eff.2.2

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
