import OAI.Computability.VPVNP.PairShrinkCallCapacity
import OAI.Computability.VPVNP.PairShrinkGeometryLimit
import OAI.Computability.VPVNP.PairShrinkRoleHandoff

/-!
# Shrinking workspace capacity for a rectangular descriptor allocation

Each old-level state is transported along its packing-lane equality. Its
hidden fields start at the end of the native scalar verifier stacks. The
polynomial upper address is fixed before specializing coefficients or choosing
compression terms, vertices, and local copy counts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallCapacity

open CursorNetwork CursorBounds Compression Compression.ShrinkMotif
open CompressorRecords Filter TraversalRows MotifConversion ShrinkCallFields

private theorem reindex_bounds {a l g : ℕ} (Z : State a l) (eqn : l = packingLaneBits a g) :
    let X : State a (packingLaneBits a g) := eqn ▸ Z
    X.positions = Z.positions ∧ X.maxWireWidth = Z.maxWireWidth := by
  subst l
  exact ⟨rfl, rfl⟩

/-- The real old child row lies inside the terminal reservation whenever its
layer is the published prefix of the complete selected row list. -/
theorem layer_addresses {a g : ℕ} (X : State a g) (cap firstRow : ℕ)
    (before after : List Layer) (current : Layer) (count : current.count = X.positions)
    (v : X.network.Site) :
    firstRow + words cap before + (cap + 2) * PortRefresh.ArgumentAddress.siteOrdinal X v <
      firstRow + words cap (before ++ current :: after) := by
  have ord : PortRefresh.ArgumentAddress.siteOrdinal X v < X.positions := by
    unfold PortRefresh.ArgumentAddress.siteOrdinal State.positions
    rw [Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv g), Fintype.card_fin]
    have hb := (X.baseIndex v.1).isLt
    have hl := (bitWordFinEquiv g v.2).isLt
    calc
      _ < (X.baseIndex v.1).val * 2 ^ g + 2 ^ g := Nat.add_lt_add_left hl _
      _ = ((X.baseIndex v.1).val + 1) * 2 ^ g := (Nat.succ_mul ..).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hb
  have step := Nat.mul_lt_mul_of_pos_left (count ▸ ord) (by omega : 0 < cap + 2)
  simp only [words, List.map_append, List.map_cons, List.sum_append, List.sum_cons,
    Nat.mul_add]
  omega

open BurstRAM in
open scoped Fin.CommRing in
/-- Both words produced by the hidden handoff have their exact natural
values in the reserved region, including the square stride. -/
theorem handoff_words {w n motifs : ℕ} (G : LeafArena.Regions)
    (room : mapBase G (Fintype.card LeafStartup.ScalarPort) n + extent motifs n < 2 ^ w) :
    (VertexLevel.hiddenBaseWord (G.cacheBase : Word w) (n : Word w)).val =
      mapBase G (Fintype.card LeafStartup.ScalarPort) n ∧
      ((n : Word w) * (n : Word w)).val = n * n := by
  have baseFit : mapBase G (Fintype.card LeafStartup.ScalarPort) n < 2 ^ w := by omega
  have strideFit : n * n < 2 ^ w := by
    unfold extent at room
    rw [pow_two] at room
    omega
  rw [VertexLevel.hiddenBaseWord_cast, ← Nat.cast_mul]
  exact ⟨Nat.mod_eq_of_lt baseFit, Nat.mod_eq_of_lt strideFit⟩

variable {k : Type} [_root_.Field k] {S : BlockSchedule k}

open Classical in
/-- Scratch and copy bound used by the actual selected map. -/
noncomputable abbrev SelectedFits {a g : ℕ} (X : State a (packingLaneBits a g))
    (B : S.Templates) (sel : X.ShrinkSelection B.shrink) (m : X.packingData.Motif)
    (G : LeafArena.Regions) (b n limit older pitch : ℕ) : Prop :=
  let demand := X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m
  let scratch := ShrinkCallHeader.scratch X (mapBase G (Fintype.card LeafStartup.ScalarPort) n)
    (n * n) G.histBase
  Fits (w := wordBits b n) (n := n) (limit := limit) (u := repetitions B.shrink demand)
    (t := Fintype.card B.Entry) B.shrink demand (sel m).val scratch
      (ShrinkMotifOrder.stateNumber X m).val (ShrinkCallHeader.cdBase X m G.arguments older pitch)

/-- The terminal layout with the dedicated map reserve fits a live word.
The scalar cache and all its stacks precede every shrink call's hidden word. -/
theorem eventually_reserved (B : S.Templates) (u : PairExponents B.growthConstant)
    (D : DescriptorSpace.Shape) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {start : ℕ → ℕ} (hs : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let L := DescriptorSpace.cursorLayout D b S.steps u.θ (start n) n
        ∀ z : (B.execute f hf T hT X).Choices,
          let rows := words B.recordLimit (selectedLayers B f hf T hT X z)
          let G := NativeFrame.regions (slotDegree S) n (DescriptorSpace.endAddress L)
            rows (Fintype.card B.Entry)
          mapBase G (Fintype.card LeafStartup.ScalarPort) n +
            extent (initialPositions b n * slotDegree S) n < 2 ^ wordBits b n := by
  let extra n := extent (initialPositions b n * slotDegree S) n
  have poly : PolynomiallyBounded extra := extent_bounded
    ((CursorRAM.bounded_positions b).mul (.const (slotDegree S)))
  filter_upwards [TerminalLayout.eventually_fitWithReserve B u D b hb hs
    (Fintype.card LeafStartup.ScalarPort) extra poly] with n fit
  intro base lanes labels hD hT R _ f hf X T L z rows G
  exact (fit labels hD hT R f hf z).2.2.2

open Classical in
/-- The actual admitted map has fitted fields and capacity on every selected
shrinking level. The remaining numerical row premise locates the published
child layer inside the selected DFS rows. -/
theorem eventually_selected (B : S.Templates) (u : PairExponents B.growthConstant)
    (D : DescriptorSpace.Shape) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {start : ℕ → ℕ} (hs : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
        let initial := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let L := DescriptorSpace.cursorLayout D b S.steps u.θ (start n) n
        ∀ z : (B.execute f hf T hT initial).Choices,
          let labelsN := Fintype.card B.Entry
          let ports := Fintype.card LeafStartup.ScalarPort
          let rows := words B.recordLimit (selectedLayers B f hf T hT initial z)
          let G := NativeFrame.regions (slotDegree S) n (DescriptorSpace.endAddress L) rows labelsN
          let limit := NativeFrame.postStackLimit (slotDegree S) b start labelsN ports n +
            extent (initialPositions b n * slotDegree S) n
          ∀ v ∈ executeLevels B f hf T hT initial z, ∀ {g : ℕ}
            (eqn : v.inputLanes = packingLaneBits v.inputExponent g),
            let X : State v.inputExponent (packingLaneBits v.inputExponent g) := eqn ▸ v.input
            ∀ (sel : X.ShrinkSelection B.shrink) (m : X.packingData.Motif) (older pitch : ℕ),
              (∀ site : X.network.Site,
                older + pitch * PortRefresh.ArgumentAddress.siteOrdinal X site < G.nodes) →
              SelectedFits X B sel m G b n limit older pitch := by
  let labelsN := Fintype.card B.Entry
  let ports := Fintype.card LeafStartup.ScalarPort
  let work := NativeFrame.postStackLimit (slotDegree S) b start labelsN ports
  have hb₁ : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  have cap := eventually_terminal_fits B.shrink b (slotDegree S) labelsN ports hb₁
    (workLimit := work) (NativeFrame.postStackLimit_bounded _ _ hs _ _)
  filter_upwards [cap, eventually_levels B u b hb (fieldFactor B.shrink + 1),
    NativeFrame.eventually_selected_histBase B u D b hb hs] with n fits fields hist
  intro base lanes labels hD hT R _ f hf initial T L z count wordsN rows G limit v hv g eqn
    X sel m older pitch node
  have live := fields labels hD hT R f hf z v hv
  obtain ⟨hp, hw⟩ := reindex_bounds v.input eqn
  have hhist := hist labels hD hT R f hf z (slotDegree S) count
  have endFit := NativeFrame.postStack_le wordsN hhist
  exact fits X sel m (DescriptorSpace.endAddress L) rows older pitch endFit v.oldDegree_le
    (hp ▸ live.1) (hw ▸ live.2) node

end PairSimulation.ShrinkCallCapacity

end VPVNP
end Computability
end OAI
