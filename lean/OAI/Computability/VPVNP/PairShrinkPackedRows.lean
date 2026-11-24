import OAI.Computability.VPVNP.PairShrinkSelectedCapacity
import OAI.Computability.VPVNP.CompressorSelectedDirectoryHistory
import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory
import OAI.Computability.VPVNP.PairTerminalPackedBudget
import OAI.Computability.VPVNP.PairTraversalPreorderBounds

/-!
# Child addresses in the selected packed DFS rows

The level ordinal counts the chronological compression passes. The prefix at
this ordinal ends immediately before the rows of its input state. The packed
layout uses the actual calendar size to locate the first DFS row. Its exclusive
row end also bounds every word-encoded preorder visit and its child references.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPackedRows

open BurstRAM Compression CompressorRecords CursorBounds CursorNetwork DescriptorSpace Filter
open TraversalRows TraversalRoles
open scoped Fin.CommRing
open private tag_count from OAI.Computability.VPVNP.CompressorSelectedDirectoryHistory

section Selected

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices)
local notation "levels" => executeLevels B f hf T hT X z
local notation "tags" => selected B f hf T hT X z
local notation "rows" => selectedLayers B f hf T hT X z
variable (workspace : ℕ) (i : Fin (executeLevels B f hf T hT X z).length)
local notation "L" => BlockProgram.layout B workspace X.positions T
local notation "firstRow" => endAddress L
local notation "older" => layerBase B.recordLimit firstRow tags i.val

private theorem child_address {a g : ℕ} (Z : State a g)
    (count : Z.positions = levels[i].input.positions)
    (site : Z.network.Site) :
    older + (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal Z site <
      firstRow + words B.recordLimit rows := by
  have hi : i.val < (tags).length := by
    simp only [selected, List.length_cons, List.length_map]
    exact Nat.lt_succ_of_lt i.isLt
  let current := (tags)[i.val].layer
  let before := ((tags).take i.val).map TaggedLayer.layer
  let later := ((tags).drop (i.val + 1)).map TaggedLayer.layer
  have atLevel : current.count = Z.positions :=
    (tag_count (B := B) (f := f) (hf := hf) (z := z) i).trans count.symm
  have split := List.take_append_drop (i.val + 1) (tags)
  rw [List.take_succ_eq_append_getElem hi, List.append_assoc, List.singleton_append] at split
  have exactRows : before ++ current :: later = rows := by
    simpa only [before, current, later, List.map_append, List.map_cons] using
      (congrArg (List.map TaggedLayer.layer) split).trans (selected_layers B f hf T hT X z)
  rw [← exactRows]
  exact ShrinkCallCapacity.layer_addresses Z B.recordLimit firstRow before later current
    atLevel site

/-- A selected input reindexed to its packing lane count uses the row prefix
of that same level, at every site in the old network. -/
theorem packed_layer_address {g : ℕ}
    (eqn : levels[i].inputLanes = packingLaneBits levels[i].inputExponent g) :
    let Z : State levels[i].inputExponent (packingLaneBits levels[i].inputExponent g) :=
      eqn ▸ levels[i].input
    ∀ site : Z.network.Site,
      older + (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal Z site <
        firstRow + words B.recordLimit rows := by
  intro Z site
  apply child_address B f hf T hT X z workspace i Z _ site
  have transported {a l l' : ℕ} (Y : State a l) (e : l = l') :
      (e ▸ Y : State a l').positions = Y.positions := by subst l'; rfl
  exact transported _ eqn

/-- The old node at a concrete shrinking occurrence is inside the packed
row allocation. Its address uses the selected occurrence and its true row pitch. -/
theorem packed_shrink_address (j : Fin S.steps) {g : ℕ}
    (Z : State (S.degreeExponent j.castSucc) (packingLaneBits (S.degreeExponent j.castSucc) g))
    (sel : SelectedScore.Selection B Z) (bits : List Bool)
    (atPass : levels[i] = shrinkLevel B f hf j Z sel bits) (site : Z.network.Site) :
    older + (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal Z site <
      firstRow + words B.recordLimit rows :=
  child_address B f hf T hT X z workspace i Z (by rw [atPass]; rfl) site

/-- In the final directory image the native input-header cell contains the
selected row prefix itself. The word bound gives its exact natural address. -/
theorem retained_row_base {w : ℕ} (mem : Memory w)
    (dirs : SelectedDirectoryHistory.Retained B f hf T hT X z L firstRow mem)
    (fit : firstRow + words B.recordLimit rows ≤ 2 ^ w) :
    (mem (levelStart L i.val + 14)).val = older := by
  have p := dirs.current i.val i.isLt.le
  change mem (levelStart L i.val + 14) = (older : Word w) at p
  obtain ⟨site⟩ := levels[i].input.baseNonempty
  have bound := child_address B f hf T hT X z workspace i levels[i].input rfl (site, 0)
  rw [p, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : older < 2 ^ w)]

end Selected

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- For every field specialization and selected branch, all encoded visits
and their child intervals are bounded by the end of the actual packed rows. -/
theorem eventually_preorder (u : PairExponents B.growthConstant) (b : ℕ)
    (hb : max S.laneBits 5 ≤ b) {start : ℕ → ℕ} (hstart : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
      let w := wordBits b n
      let T := blockCount (u.θ : ℝ) n
      let X := pairInput S labels hD
      let L := BlockProgram.layout B (start n) X.positions T
      ∀ (z : (B.execute f hf T hT X).Choices) (mem : Memory w),
        let layers := selectedLayers B f hf T hT X z
        let limit := endAddress L + words B.recordLimit layers
        AllRows w mem B.recordLimit (endAddress L) (endAddress L) layers →
          ∀ v, ∀ node ∈ (selectedTrees B f hf T hT X z (endAddress L) v).preorder.map
            (fun m : ℕ ↦ (m : Word w)),
            node.val + 2 ≤ limit ∧ (mem node.val).val + (mem (node.val + 1)).val ≤ limit := by
  filter_upwards [TerminalLayout.eventually_packedFit B u b hb hstart 0 (fun _ ↦ 0)
    (PolynomiallyBounded.const 0)] with n room
  intro base l labels hD hT R _ f hf w T X L z mem layers limit stored
  have packed := room labels hD hT R f hf z
  have positions : X.positions = initialPositions b n := pairInput_positions S labels hD
  have le : limit ≤ 2 ^ w := by
    change endAddress (BlockProgram.layout B (start n) X.positions T) +
      words B.recordLimit layers ≤ 2 ^ w
    rw [positions]
    have external := packed.1
    have high := packed.2.1
    let final := (B.execute f hf T hT X).finalState z
    let header := TerminalLayout.headerBase (start n) (addressBits b n)
    change endAddress (BlockProgram.layout B (start n) (initialPositions b n) T) +
      2 * words B.recordLimit layers + final.totalWidth < header at external
    change header + 32 ≤ 2 ^ w at high
    omega
  exact selected_preorder_word_bounds B f hf T hT X z (endAddress L) limit mem stored le_rfl le

end PairSimulation.ShrinkPackedRows

end VPVNP
end Computability
end OAI
