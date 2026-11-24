import OAI.Computability.VPVNP.PairSelectedPacketFormat
import OAI.Computability.VPVNP.PairTraversalRootAddress
import OAI.Computability.VPVNP.PairSimulationNodeFieldSpace

/-!
# Root and child argument frames of a selected physical vertex

The terminal site's actual packed half assignment belongs to the selected
packet format at its root address. Every newly guessed child packet has this
format and fits the fixed argument stride and the live private word space.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open NetworkKernel CompressorRecords LocalHistory NodeArguments
open Compression TraversalRows TraversalRoles

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) {lanes : ℕ} (T : ℕ)
    (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute f hf T hT X).Choices) (base : ℕ)

local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => selected B f hf T hT X z
local notation "rows" => selectedLayers B f hf T hT X z
local notation "pos" => layerBase B.recordLimit base (tags)
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z

theorem selected_lastBase : (pos) (passes).length = base + words B.recordLimit (rows).dropLast := by
  have count : (tags).length = (passes).length+1 := by simp [selected]
  rw [← selected_layers, List.dropLast_eq_take, List.length_map,count,
    Nat.add_sub_cancel,← List.map_take]
  rfl

theorem selected_endBase : (pos) ((passes).length+1) = base + words B.recordLimit (rows) := by
  have count : (tags).length = (passes).length+1 := by simp [selected]
  rw [layerBase,← count,List.take_length,selected_layers]

/-- The physical packet passed from the final endpoint gather into DFS. -/
theorem selected_root_format (v : (Y).network.Site) (h : (Y).network.Half v) :
    SelectedPacketFormat B f hf T hT X z base
      ⟨(selectedTrees B f hf T hT X z base v).address,packed (Y) v h⟩ := by
  apply (selected_format B f hf T hT X z base).2
  refine ⟨v,h,?_⟩
  rw [selectedTrees_address,selected_lastBase]
  rfl

theorem selected_packet_node {q : Packet} (format : SelectedPacketFormat B f hf T hT X z base q) :
    q.node < base + words B.recordLimit (rows) := by
  rw [← selected_endBase]
  exact format.node_lt rfl

/-- The whole placed child list, including an empty fiber, meets the
format and fit premises of the histogram-budgeted frontier transition. -/
theorem selected_children_fit {n w : ℕ} (regions : LeafArena.Regions)
    (start : n ≤ regions.arguments.start)
    (stride : frameStride (slotDegree S) n ≤ regions.arguments.stride)
    (wordFit : regions.histBase ≤ 2 ^ w)
    (nodes : base + words B.recordLimit (rows) ≤ regions.nodes)
    (width : B.growthConstant ^ T * (X.maxWireWidth + 1) ≤ n) (i : Fin (passes).length) :
    let v := (passes)[i]
    let reader := originReader B f hf v.origin v.term
    let input := fun u h => Packet.mk
      (sitePointers B.recordLimit ((pos) i.val) (siteOrder v.input) u).1
      (packed v.input u h)
    ∀ u a q, q ∈ children reader input u a →
      SelectedPacketFormat B f hf T hT X z base q ∧ q.Fits regions.arguments w n := by
  intro v reader input u a q h
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
  let child := (reader.order.children u).entries j
  let packet := input child.val (a child.val child.prop)
  have fmt : SelectedPacketFormat B f hf T hT X z base packet :=
    (selected_format B f hf T hT X z base).1 i packet ⟨child.val,_,rfl⟩
  have below := (selected_packet_node B f hf T hT X z base fmt).trans_le nodes
  have fit := regions.node_before below
  have width' := ((executeLevels_limits B f hf T hT X z v (List.getElem_mem ..)).2).trans width
  have size : packet.bits.length ≤ regions.arguments.stride :=
    (packed_length_le v.input child.val _).trans
      (((Nat.mul_le_mul (Nat.mul_le_mul_left 2 v.oldDegree_le)
      width').trans (Nat.le_succ _)).trans stride)
  exact ⟨fmt,start.trans (Nat.le_add_right _ _),size,
    (Nat.add_le_add_left size _).trans (fit.trans wordFit)⟩

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
