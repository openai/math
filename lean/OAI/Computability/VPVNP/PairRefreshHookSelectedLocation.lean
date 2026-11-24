import OAI.Computability.VPVNP.CompressorRefreshTraversalChild
import OAI.Computability.VPVNP.CompressorRecordRefreshArgumentSite
import OAI.Computability.VPVNP.CompressorRefreshCopyGeometry
import OAI.Computability.VPVNP.PairTraversalControllerInputs
import OAI.Computability.VPVNP.PairTraversalRoleExecution

/-!
# Locating a selected refresh port in the physical DFS table

The typed level directories have exactly the tagged layers of the chosen
compressor branch. At an occurrence of a degree refresh the port ordinal
therefore names a live output row. Its unique child has the same ordinal
at the preceding layer base.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.RefreshHook.SelectedLocation

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh CompressorRecords
open PortRefresh NewSlots LocalHistory TraversalRoles TraversalRows TraversalControllerInputs
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
  {g n w : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n) (initial : State (S.degreeExponent 0) n)
  (z : (B.execute f hf T hT initial).Choices) (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh) (encoded : List Bool)
  (port : (X.Base × BitWord g) × Fin (2 ^ S.portExponent))

local notation "levels" => executeLevels B f hf T hT initial z
local notation "tags" => TraversalRoles.selected B f hf T hT initial z
local notation "v" => RefreshPlacement.traversalLevel f hf X choice encoded
local notation "site" => (sites (D := 2 ^ S.portExponent) X.baseIndex (bitWordFinEquiv g) port)
local notation "leaf" => TaggedLayer.mk (leafLayer (siteOrder initial)) Role.cursor
local notation "cap" => B.recordLimit

theorem live_port : (site).val < (levelLayer B f hf v).count := by
  rw [levelLayer_count]
  change (site).val < Fintype.card (((v).pass.next (v).term).Base × BitWord g)
  rw [Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv g), Fintype.card_fin]
  have card := CopyGeometry.base_count X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2 choice
  change Fintype.card ((v).pass.next (v).term).Base =
    Fintype.card X.Base * 2 ^ S.portExponent at card
  rw [card]
  exact (site).isLt

variable (stage : Fin (executeLevels B f hf T hT initial z).length)
  (occurrence : (executeLevels B f hf T hT initial z)[stage] =
    RefreshPlacement.traversalLevel f hf X choice encoded)
  {pub : Fin 11 → BurstRAM.Word w} {mem : Memory w} {H first pitch offset base : ℕ}

include occurrence in
/-- The actual directory bank locates this selected output identifier in the same
layer sequence and at the same absolute row address as the vertex controller. -/
theorem locate (ds : (i : Fin (levels).length) → LevelDirectory levels[i] mem base)
    (resident : Resident pub mem H first pitch offset cap base leaf (levelFibers levels ds))
    (fits : base + tagWords cap tags < 2 ^ w) :
    let fibers := levelFibers levels ds
    let table := leaf :: fibers.map Prod.fst
    ∃ j : Fin table.length, ∃ id : Fin table[j].layer.count,
      Resident pub mem H first pitch offset cap base leaf fibers ∧
      j.val = stage.val + 1 ∧ id.val = (site).val ∧
      ((tags).length - 1) - (stage.val + 1) = fibers.length - (stage.val + 1) ∧
      address cap (layerBase cap base tags (stage.val + 1)) (site).val =
        address cap (layerBase cap base table j.val) id.val ∧
      layerBase cap base table (fibers.length + 1) < 2 ^ w := by
  let fibers := levelFibers levels ds
  let table := leaf :: fibers.map Prod.fst
  have tagEq : table = tags := by
    change leaf :: (levelFibers levels ds).map Prod.fst = _
    rw [levelFibers_tags]
    rfl
  have lengthEq : fibers.length = (levels).length := by simp [fibers, levelFibers]
  have tagLength : (tags).length = fibers.length + 1 := by simp [← tagEq, table]
  let j : Fin table.length := ⟨stage.val + 1, by
    have hs := stage.isLt
    simp only [table, List.length_cons, List.length_map, lengthEq]
    omega⟩
  have layerEq : table[j].layer = levelLayer B f hf v := by
    change (table[stage.val + 1]'j.isLt).layer = _
    simp only [table, List.getElem_cons_succ, List.getElem_map, fibers, levelFibers,
      List.getElem_ofFn]
    exact congrArg (levelLayer B f hf) occurrence
  let id : Fin table[j].layer.count := ⟨(site).val, by
    rw [layerEq]
    exact live_port B f hf X choice encoded port⟩
  refine ⟨j, id, resident, rfl, rfl, ?_, ?_, ?_⟩
  · change (tags).length - 1 - (stage.val + 1) = fibers.length - (stage.val + 1)
    rw [tagLength, Nat.add_sub_cancel]
  · change address cap (layerBase cap base tags (stage.val + 1)) (site).val =
      address cap (layerBase cap base table (stage.val + 1)) (site).val
    rw [tagEq]
  · change layerBase cap base table (fibers.length + 1) < 2 ^ w
    rw [tagEq, ← tagLength]
    simpa only [layerBase, List.take_length, tagWords] using fits

include occurrence in
theorem child_row (rows : AllRows w mem cap base base (selectedLayers B f hf T hT initial z)) :
    let parent := address cap (layerBase cap base tags (stage.val + 1)) (site).val
    let child := address cap (layerBase cap base tags stage.val) (site).val
    DFS.Row mem parent (parent + 2) [(child : BurstRAM.Word w)] :=
  RefreshPlacement.selected_row f hf X choice encoded T hT initial z rows stage occurrence
    ⟨(site).val, live_port B f hf X choice encoded port⟩

end PairSimulation.RefreshHook.SelectedLocation

end

end VPVNP
end Computability
end OAI
