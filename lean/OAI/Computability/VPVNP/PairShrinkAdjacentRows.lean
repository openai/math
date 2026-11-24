import OAI.Computability.VPVNP.PairShrinkPackedParent

/-!
# Disjoint child and parent rows at a selected shrinking occurrence

The old site ordinal belongs to the input layer at the physical pass index.
The next selected prefix begins after every row of that layer. This separates
every child packet address from the output address used by a resident party.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPackedRows

open Compression CompressorRecords DescriptorSpace TraversalRows TraversalRoles
open PortRefresh.ArgumentAddress
open private tag_count from OAI.Computability.VPVNP.CompressorSelectedDirectoryHistory

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices)
variable (workspace : ℕ) (cur : Fin (executeLevels B f hf T hT X z).length)
variable (j : Fin S.steps) {g : ℕ}
variable (Z : State (S.degreeExponent j.castSucc) (packingLaneBits (S.degreeExponent j.castSucc) g))
variable (sel : SelectedScore.Selection B Z) (bits : List Bool)
local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => selected B f hf T hT X z
local notation "firstRow" => endAddress (BlockProgram.layout B workspace X.positions T)
local notation "older" => layerBase B.recordLimit firstRow tags cur.val
local notation "later" => layerBase B.recordLimit firstRow tags (cur.val + 1)
local notation "pitch" => B.recordLimit + 2
local notation "Y" => Z.shrinkNext B.shrink (S.shrink j) sel

/-- Every old site starts strictly before the selected successor layer. -/
theorem packed_child_before_successor (occurrence : passes[cur] = shrinkLevel B f hf j Z sel bits)
    (child : Z.network.Site) : older + (pitch) * siteOrdinal Z child < later := by
  have hi : cur.val < (tags).length := by
    simp only [selected, List.length_cons, List.length_map]
    exact Nat.lt_succ_of_lt cur.isLt
  let current := (tags)[cur.val].layer
  let before := ((tags).take cur.val).map TaggedLayer.layer
  have count : current.count = Z.positions := by
    have h := tag_count (B := B) (f := f) (hf := hf) (z := z) cur
    rw [occurrence] at h
    exact h
  have bounds := ShrinkCallCapacity.layer_addresses Z B.recordLimit firstRow before [] current
    count child
  simpa only [layerBase, List.take_succ_eq_append_getElem hi, List.map_append, List.map_cons,
    List.map_nil, before, current] using bounds

/-- In particular, updating any old child packet cannot address the parent's
row, even when that parent is the last output site of the branch. -/
theorem packed_child_before_parent (occurrence : passes[cur] = shrinkLevel B f hf j Z sel bits)
    (child : Z.network.Site) (parent : (Y).network.Site) :
    older + (pitch) * siteOrdinal Z child < later + (pitch) * siteOrdinal (Y) parent :=
  lt_of_lt_of_le
    (packed_child_before_successor B f hf T hT X z workspace cur j Z sel bits occurrence child)
    (Nat.le_add_right _ _)

end PairSimulation.ShrinkPackedRows

end VPVNP
end Computability
end OAI
