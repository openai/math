import OAI.Computability.VPVNP.CompressorRefreshLevelDirectory
import OAI.Computability.VPVNP.PairTraversalRoles

/-!
# Singleton child rows of a selected refresh

Promotion retains the preceding site's numerical identifier. In the physical
DFS arena the corresponding child address is obtained from the preceding layer
base and the same identifier as the popped parent.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshPlacement

open PairSimulation BurstRAM Compression Compression.Refresh Compression.DegreeRefresh
  PairSimulation.LocalHistory PairSimulation.TraversalRows
open scoped Fin.CommRing

open private placementLayer from OAI.Computability.VPVNP.PairTraversalStageSize
open private preimage_singleton from OAI.Computability.VPVNP.CompressorRefreshPlacementRows
open private actualPass from OAI.Computability.VPVNP.CompressorRefreshLevelDirectory

variable {g : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (bits : List Bool)

/-- The selected refresh pass packaged with its input state, promoted output, refresh origin,
term choice and branch bits for DFS traversal. -/
abbrev traversalLevel : SelectedLevel B f hf :=
  ⟨_, _, _, _, X, actualPass f hf X, .refresh X, choice, bits⟩

/-- This site has exactly its own ordinal as its child, including at nonzero
residual - lane offsets. The proof identifies the stored order using the native
identity preimage list. -/
theorem layer_singleton (i : Fin (levelLayer B f hf (traversalLevel f hf X choice bits)).count) :
    (levelLayer B f hf (traversalLevel f hf X choice bits)).ids i = [i.val] := by
  classical
  let prev := siteOrder X
  let next := siteOrder ((actualPass f hf X).next choice)
  let t := (actualPass f hf X).step.term choice
  let place := t.place
  let width := X.positions
  have counts := site_counts f hf X choice
  have oldRoom : prev.length ≤ 2 ^ width := counts.1.trans_le (Nat.le_of_lt Nat.lt_two_pow_self)
  have newRoom : next.length ≤ 2 ^ width := counts.2.trans_le (Nat.le_of_lt Nat.lt_two_pow_self)
  have fit : i.val < prev.length := i.isLt.trans_eq (counts.2.trans counts.1.symm)
  have hi : i.val < 2 ^ width := fit.trans_le oldRoom
  let j : Fin next.length := i
  let v := next.entries j
  have code : siteWord width next v = (i.val : BurstRAM.Word width) := by
    change Fin.ofNat (2 ^ width) (next.entries.symm (next.entries j)).val = Fin.ofNat
      (2 ^ width) j.val
    rw [Equiv.symm_apply_apply]
  have ordered := preimagePrefix_eq_orderedIds prev next place id
    (placement_identity (w := width) f hf X choice) oldRoom newRoom v
  have single := preimage_singleton oldRoom (siteWord width next v) (by
    rw [code, Fin.val_natCast, Nat.mod_eq_of_lt hi]; exact fit)
  have numeric := congrArg (List.map Fin.val) (ordered.symm.trans single)
  rw [code] at numeric
  have value (u : X.network.Site) : (siteWord width prev u).val = (prev.entries.symm u).val :=
    Nat.mod_eq_of_lt ((prev.entries.symm u).isLt.trans_le oldRoom)
  simp only [orderedIds, List.map_ofFn, Function.comp_def, value, List.map_cons, List.map_nil,
    Fin.val_natCast, Nat.mod_eq_of_lt hi] at numeric
  exact numeric

/-- A row returned by the native traversal arena points directly to the matching
node in the preceding layer at the actual exclusive row stride. -/
theorem singleton_row {w cap prev base : ℕ} {m : Memory w}
    (rows : (levelLayer B f hf (traversalLevel f hf X choice bits)).Rows w m cap prev base)
    (i : Fin (levelLayer B f hf (traversalLevel f hf X choice bits)).count) :
    DFS.Row m (address cap base i.val) (address cap base i.val + 2)
      [(address cap prev i.val : BurstRAM.Word w)] := by
  simpa only [childWords, layer_singleton f hf X choice bits i, List.map_cons, List.map_nil] using
    (rows i).2

open TraversalRoles

private theorem successor_rows {w cap previous base : ℕ} {m : Memory w} {layers : List TaggedLayer}
    (rows : AllRows w m cap previous base (layers.map TaggedLayer.layer)) (i : ℕ)
      (hi : i + 1 < layers.length) :
    layers[i + 1].layer.Rows w m cap (layerBase cap base layers i) (layerBase cap base layers
      (i + 1)) := by
  induction layers generalizing previous base i with
  | nil => simp at hi
  | cons L layers ih =>
    change L.layer.Rows w m cap previous base ∧ AllRows w m cap base (endPos cap base L.layer)
      (layers.map TaggedLayer.layer) at rows
    cases i with
    | zero =>
      cases layers with
      | nil => simp at hi
      | cons H tail =>
        simpa only [List.getElem_cons_succ, List.getElem_cons_zero, layerBase_cons,
          layerBase_zero] using rows.2.1
    | succ i =>
      simpa only [List.getElem_cons_succ, layerBase_cons] using
        ih rows.2 i (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hi)

/-- Extract the singleton row directly from the all-level memory guarantee of the
native arena, at the two layer bases used by the popped-node locator. -/
theorem selected_row {n w base : ℕ} {m : Memory w} (T : ℕ) (hT : T * S.laneBits ≤ n)
    (initial : State (S.degreeExponent 0) n) (z : (B.execute f hf T hT initial).Choices)
    (rows : AllRows w m B.recordLimit base base (selectedLayers B f hf T hT initial z))
    (stage : Fin (executeLevels B f hf T hT initial z).length)
    (refresh : (executeLevels B f hf T hT initial z)[stage] = traversalLevel f hf X choice bits)
    (i : Fin (levelLayer B f hf (traversalLevel f hf X choice bits)).count) :
    let tags := selected B f hf T hT initial z
    let parent := address B.recordLimit (layerBase B.recordLimit base tags (stage.val + 1)) i.val
    let child := address B.recordLimit (layerBase B.recordLimit base tags stage.val) i.val
    DFS.Row m parent (parent + 2) [(child : BurstRAM.Word w)] := by
  let tags := selected B f hf T hT initial z
  have all : AllRows w m B.recordLimit base base (tags.map TaggedLayer.layer) := by
    rwa [selected_layers]
  have bound : stage.val + 1 < tags.length := by simp [tags, selected]
  have layer : tags[stage.val + 1].layer = levelLayer B f hf
    (traversalLevel f hf X choice bits) := by
    simp only [tags, selected, List.getElem_cons_succ, List.getElem_map]
    exact congrArg (levelLayer B f hf) refresh
  have row := successor_rows all stage.val bound
  rw [layer] at row
  exact singleton_row f hf X choice bits row i

end CompressorRecords.RefreshPlacement

end

end VPVNP
end Computability
end OAI
