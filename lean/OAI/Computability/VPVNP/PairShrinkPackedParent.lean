import OAI.Computability.VPVNP.PairShrinkPackedRows

/-!
# The output packet of a selected shrink in the packed terminal arena

The output sites of a pass occupy its successor layer, including when that
layer is terminal. Their slot widths are the subdivided supply widths of the
admitted motif terms or the zero widths on cyclic padding arcs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPackedRows

open BurstRAM Compression CompressorRecords CursorBounds CursorNetwork DescriptorSpace Filter
open TraversalRows TraversalRoles MotifConversion ShrinkMotif

section Rows

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
local notation "rows" => selectedLayers B f hf T hT X z
local notation "Y" => Z.shrinkNext B.shrink (S.shrink j) sel
local notation "firstRow" => endAddress (BlockProgram.layout B workspace X.positions T)

/-- Each output site's argument address is in the selected row reservation,
at the prefix immediately after the input layer of this shrink. -/
theorem packed_parent_address (occurrence : passes[cur] = shrinkLevel B f hf j Z sel bits)
    (site : (Y).network.Site) :
    layerBase B.recordLimit firstRow tags (cur.val + 1) +
      (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal (Y) site <
      firstRow + words B.recordLimit rows := by
  have hi : cur.val + 1 < (tags).length := by
    simp only [selected, List.length_cons, List.length_map]
    exact Nat.succ_lt_succ cur.isLt
  let current := (tags)[cur.val + 1].layer
  let before := ((tags).take (cur.val + 1)).map TaggedLayer.layer
  let later := ((tags).drop (cur.val + 1 + 1)).map TaggedLayer.layer
  have count : current.count = (Y).positions := by
    simp only [current, selected, List.getElem_cons_succ, List.getElem_map, levelLayer_count]
    rw [show passes[cur.val] = shrinkLevel B f hf j Z sel bits from occurrence]
    rfl
  have split := List.take_append_drop (cur.val + 1 + 1) (tags)
  rw [List.take_succ_eq_append_getElem hi, List.append_assoc, List.singleton_append] at split
  have exactRows : before ++ current :: later = rows := by
    simpa only [before, current, later, List.map_append, List.map_cons] using
      (congrArg (List.map TaggedLayer.layer) split).trans (selected_layers B f hf T hT X z)
  rw [← exactRows]
  exact ShrinkCallCapacity.layer_addresses (Y) B.recordLimit firstRow before later current
    count site

end Rows

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Maximum width of the selected outgoing slots. The local conversion block
bounds the whole supply word before the layout subdivides it. -/
theorem shrinkNext_width_le (j : Fin S.steps) {g : ℕ}
    (Z : State (S.degreeExponent j.castSucc) (packingLaneBits (S.degreeExponent j.castSucc) g))
    (sel : SelectedScore.Selection B Z) :
    (Z.shrinkNext B.shrink (S.shrink j) sel).maxWireWidth ≤
      fieldFactor B.shrink * (Z.maxWireWidth + 1) := by
  classical
  let d := 2 ^ S.degreeExponent j.castSucc
  let c := 2 * d + 1
  let layout := Z.packingData.shrinkTermLayout B.shrink Z.shrinkNumber Z.packingWidth sel
  apply Finset.sup_le
  intro e _
  exact Z.packingData.shrinkSlotWidth_le (State.two_le_packingColors _) (Nat.two_pow_pos _)
    Z.shrinkNumber Z.packingWidth (fun _ ↦ Z.width_le_maxWireWidth _) B.shrink sel layout
    (subdivisions d c (2 ^ S.degreeExponent j.succ))
    (Z.shrinkStateIndex (S.shrink j) layout).outgoing e

/-- The same length threshold covers every output site, including the sites
of the final shrink, before any coefficient assignment or branch choice. -/
theorem eventually_parent_width (u : PairExponents B.growthConstant) (b : ℕ)
    (hb : max S.laneBits 5 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      ∀ z : (B.execute f hf T hT X).Choices,
        ∀ (cur : Fin (executeLevels B f hf T hT X z).length) (j : Fin S.steps) {g : ℕ}
          (Z : State (S.degreeExponent j.castSucc)
            (packingLaneBits (S.degreeExponent j.castSucc) g))
          (sel : SelectedScore.Selection B Z) (bits : List Bool),
          (executeLevels B f hf T hT X z)[cur] = shrinkLevel B f hf j Z sel bits →
            (Z.shrinkNext B.shrink (S.shrink j) sel).maxWireWidth ≤ n ∧
              2 ^ S.degreeExponent j.succ ≤ slotDegree S := by
  filter_upwards [ShrinkCallCapacity.eventually_levels B u b hb (fieldFactor B.shrink)]
    with n bounds
  intro base lanes labels hD hT R _ f hf X T z cur j g Z sel bits occurrence
  let vs := executeLevels B f hf T hT X z
  have input := (bounds labels hD hT R f hf z vs[cur] (List.getElem_mem cur.isLt)).2
  have atLevel : vs[cur] = shrinkLevel B f hf j Z sel bits := occurrence
  rw [atLevel] at input
  exact ⟨(shrinkNext_width_le B j Z sel).trans input,
    (shrinkLevel B f hf j Z sel bits).outputDegree_le⟩

end PairSimulation.ShrinkPackedRows

end VPVNP
end Computability
end OAI
