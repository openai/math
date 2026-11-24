import OAI.Computability.VPVNP.PairShrinkSelectedCapacity
import OAI.Computability.VPVNP.PairTerminalPackedBudget
import OAI.Computability.VPVNP.PairShrinkPackedRows

/-!
# Shrinking map capacity at the packed directory's physical row end

The compressor publishes exactly its live calendar rows. The first DFS row
follows this tight directory. Its end fixes the terminal argument frames,
histogram, cache and stacks, and thus the natural base of the shrinking
worker's private maps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallCapacity

open BurstRAM Compression CursorBounds CursorNetwork CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles Filter ShrinkCallFields Compression.ShrinkMotif
open private reindex_bounds from OAI.Computability.VPVNP.PairShrinkSelectedCapacity
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k}
variable (B : S.Templates) (u : PairExponents B.growthConstant)
variable (b : ℕ) (hb : max S.laneBits 5 ≤ b) {start : ℕ → ℕ} (hs : PolynomiallyBounded start)

local notation "P" => initialPositions b
local notation "T" => blockCount (u.θ : ℝ)
local notation "degree" => slotDegree S
local notation "ports" => Fintype.card LeafStartup.ScalarPort
local notation "labelCount" => Fintype.card B.Entry
local notation "work" => NativeFrame.postStackLimit degree b start labelCount ports
local notation "extra" => fun n ↦ extent (P n * degree) n

include hb hs in
/-- The runtime cache word and live length produce the exact private map
base and square stride. All map storage then ends before the word modulus. -/
theorem eventually_packed_handoff :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : T n * S.laneBits ≤ lanes) (R : Type*) [CommRing R] (f : B.Entry → R)
      (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let L := BlockProgram.layout B (start n) (P n) (T n)
      ∀ z : (B.execute f hf (T n) hT X).Choices,
        let rows := words B.recordLimit (selectedLayers B f hf (T n) hT X z)
        let G := NativeFrame.regions degree n (endAddress L) rows labelCount
        let w := wordBits b n
        mapBase G ports n + extra n < 2 ^ w ∧
          (VertexLevel.hiddenBaseWord (G.cacheBase : Word w) (n : Word w)).val = mapBase G ports n ∧
          ((n : Word w) * (n : Word w)).val = n * n := by
  have hsize := extent_bounded ((CursorRAM.bounded_positions b).mul (.const degree))
  filter_upwards [TerminalLayout.eventually_packedFit B u b hb hs ports extra hsize]
    with n room
  intro base lanes labels hD hT R _ f hf X L z rows G w
  have bound : mapBase G ports n + extra n < 2 ^ w := (room labels hD hT R f hf z).2.2.2.1
  exact ⟨bound, handoff_words G bound⟩

/-- Read the two input words of the map handoff from the terminal geometry
written for the packed directory and recover the histogram pointer as well. -/
theorem packed_private_words {w n : ℕ} (positions blocks rows pitch baseRadix laneRadix : ℕ)
    (mem : Memory w) (header role span : Word w) (pub : Fin 11 → Word w)
    (priv : Word w → Word w) (geometry : Word w)
    (live : (pub 6).val = n) (labels : (pub 9).val = labelCount) :
    let L := BlockProgram.layout B (start n) positions blocks
    let G := NativeFrame.regions degree n (endAddress L) rows labelCount
    NativeFrame.Readback mem header (endAddress L) rows pitch baseRadix laneRadix span →
    endAddress L + rows < 2 ^ w →
    mapBase G ports n + extent (positions * degree) n < 2 ^ w →
    (∀ i : Fin 12, priv (geometry + (i.val : Word w)) =
      NativeFrame.fields degree pub header role mem i) →
      (VertexLevel.hiddenBaseWord (priv (geometry + 8)) (priv (geometry + 9))).val =
        mapBase G ports n ∧
        (priv (geometry + 9) * priv (geometry + 9)).val = n * n ∧
          priv (geometry + 11) = (G.histBase : Word w) := by
  intro L G read rowFit room fields
  have eqn := read.regions_eq degree pub n labelCount live labels rowFit
  have hc := fields 8
  change priv (geometry + 8) = ((NativeFrame.fromHeader degree pub header mem).cacheBase : Word w)
    at hc
  rw [eqn] at hc
  have hn : priv (geometry + 9) = (n : Word w) := (fields 9).trans
    (live ▸ (Fin.cast_val_eq_self _).symm)
  have hh := fields 11
  change priv (geometry + 11) = ((NativeFrame.fromHeader degree pub header mem).histBase : Word w)
    at hh
  rw [eqn] at hh
  rw [hc, hn]
  obtain ⟨base, stride⟩ := handoff_words G room
  exact ⟨base, stride, hh⟩

include hb hs in
/-- The packed first-row address is at most the rectangular allocation end.
Both layouts use the same selected DFS words, so the previously bounded
histogram also bounds the actual post-stack start. -/
theorem eventually_packed_workBase :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : T n * S.laneBits ≤ lanes) (R : Type*) [CommRing R] (f : B.Entry → R)
      (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let L := BlockProgram.layout B (start n) (P n) (T n)
      ∀ z : (B.execute f hf (T n) hT X).Choices,
        let rows := words B.recordLimit (selectedLayers B f hf (T n) hT X z)
        let G := NativeFrame.regions degree n (endAddress L) rows labelCount
        mapBase G ports n ≤ work n := by
  filter_upwards [NativeFrame.eventually_selected_histBase B u (BlockProgram.allocationShape B)
    b hb hs] with n bounds
  intro base lanes labels hD hT R _ f hf X L z rows G
  let upper := cursorLayout (BlockProgram.allocationShape B) b S.steps u.θ (start n) n
  have end_le : endAddress L ≤ endAddress upper := BlockProgram.allocation_end B _ _ _
  apply NativeFrame.postStack_le
  have hist := bounds labels hD hT R f hf z degree labelCount
  refine le_trans ?_ hist
  change n + (endAddress L + rows) * (2 * degree * n + 1) ≤
    n + (endAddress upper + rows) * (2 * degree * n + 1)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.add_le_add_right end_le rows)) n

open Classical in
/-- Fitted maps indexed by the transported input of a selected level. -/
structure SelectedAt {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
    (v : SelectedLevel B f hf) (G : LeafArena.Regions) (b n limit older pitch : ℕ) : Prop where
  fits : ∀ {g : ℕ} (eqn : v.inputLanes = packingLaneBits v.inputExponent g),
    let X : State v.inputExponent (packingLaneBits v.inputExponent g) := eqn ▸ v.input
    ∀ (sel : X.ShrinkSelection B.shrink) (m : X.packingData.Motif),
      SelectedFits X B sel m G b n limit older pitch

open Classical in
include hb hs in
/-- All child addresses and the scratch base are the ones stored for this
selected level of the packed calendar. The capacity limit is the exclusive
end of the dedicated post-stack reserve on this very branch. -/
theorem eventually_packed_selected :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : T n * S.laneBits ≤ lanes) (R : Type*) [CommRing R] (f : B.Entry → R)
      (hf : B.IsSolution f),
      let initial := pairInput S labels hD
      let firstRow := endAddress (BlockProgram.layout B (start n) (P n) (T n))
      ∀ z : (B.execute f hf (T n) hT initial).Choices,
        let vs := executeLevels B f hf (T n) hT initial z
        let tags := selected B f hf (T n) hT initial z
        let rows := words B.recordLimit (selectedLayers B f hf (T n) hT initial z)
        let G := NativeFrame.regions degree n firstRow rows labelCount
        let limit := mapBase G ports n + extra n
        ∀ i : Fin vs.length, SelectedAt B vs[i] G b n limit
          (layerBase B.recordLimit firstRow tags i.val) (B.recordLimit + 2) := by
  have hb₁ : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  have capacity := eventually_capacity B.shrink b hb₁ degree
    (NativeFrame.postStackLimit_bounded degree b hs labelCount ports)
  filter_upwards [capacity, eventually_levels B u b hb (fieldFactor B.shrink + 1),
    eventually_packed_workBase B u b hb hs, eventually_packed_handoff B u b hb hs,
    eventually_ge_atTop 1] with n cap levels bases handoff hn
  intro base lanes labels hD hT R _ f hf initial firstRow z vs tags rows G limit i
  let v := vs[i]
  let older := layerBase B.recordLimit firstRow tags i.val
  constructor
  intro g eqn X sel m
  obtain ⟨hp, hw⟩ := reindex_bounds v.input eqn
  have live := levels labels hD hT R f hf z v (List.getElem_mem i.isLt)
  have hWidth : (fieldFactor B.shrink + 1) * (X.maxWireWidth + 1) ≤ n := hw ▸ live.2
  have hPos : X.positions ≤ P n := hp ▸ live.1
  have small : limit ≤ work n + extra n :=
    Nat.add_le_add_right (bases labels hD hT R f hf z) _
  have actual : MapWorkspace.Capacity B.shrink (wordBits b n) n limit :=
    ⟨cap.selectorBits, cap.demandBits, cap.payloadBits,
      (handoff labels hD hT R f hf z).1, fun a ha ↦ cap.fields a (ha.trans small)⟩
  have hist : G.histBase + labelCount ≤ mapBase G ports n := histogram_before G ports n
  have hx : X.maxWireWidth ≤ n := by rw [Nat.add_mul, Nat.one_mul] at hWidth; omega
  have below (site : X.network.Site) (zhalf : X.network.Half site) :
      G.arguments.base (older + (B.recordLimit + 2) *
        PortRefresh.ArgumentAddress.siteOrdinal X site) +
          (NodeArguments.packed X site zhalf).length ≤ mapBase G ports n := by
    have row := ShrinkPackedRows.packed_layer_address B f hf (T n) hT initial z
      (start n) i eqn site
    rw [show initial.positions = P n from pairInput_positions S labels hD] at row
    have len : (NodeArguments.packed X site zhalf).length ≤ G.arguments.stride :=
      (NodeArguments.packed_length_le X site zhalf).trans
        ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 v.oldDegree_le) hx).trans (Nat.le_succ _))
    exact (Nat.add_le_add_left len _).trans ((G.node_before row).trans
      ((Nat.le_add_right _ _).trans hist))
  simpa only [SelectedFits, pow_two, limit] using fits X B.shrink sel m hn hist le_rfl
    (motif_count X hPos v.oldDegree_le) hWidth actual G.arguments older (B.recordLimit + 2) below

open Classical in
include hb hs in
/-- At a concrete native shrinking occurrence the selected motif supplies
its admitted term and the old layer base and pitch are the published ones. -/
theorem eventually_packed_occurrence :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : T n * S.laneBits ≤ lanes) (R : Type*) [CommRing R] (f : B.Entry → R)
      (hf : B.IsSolution f),
      let initial := pairInput S labels hD
      let firstRow := endAddress (BlockProgram.layout B (start n) (P n) (T n))
      ∀ z : (B.execute f hf (T n) hT initial).Choices,
        let vs := executeLevels B f hf (T n) hT initial z
        let tags := selected B f hf (T n) hT initial z
        let rows := words B.recordLimit (selectedLayers B f hf (T n) hT initial z)
        let G := NativeFrame.regions degree n firstRow rows labelCount
        ∀ (i : Fin vs.length) (j : Fin S.steps) {g : ℕ}
          (X : State (S.degreeExponent j.castSucc)
            (packingLaneBits (S.degreeExponent j.castSucc) g))
          (sel : SelectedScore.Selection B X) (bits : List Bool),
          vs[i] = shrinkLevel B f hf j X sel bits →
          ∀ m : X.packingData.Motif, SelectedFits X B sel m G b n (mapBase G ports n + extra n)
            (layerBase B.recordLimit firstRow tags i.val) (B.recordLimit + 2) := by
  filter_upwards [eventually_packed_selected B u b hb hs] with n fits
  intro base lanes labels hD hT R _ f hf initial firstRow z vs tags rows G i j g X sel bits atPass m
  have h := fits labels hD hT R f hf z i
  change SelectedAt B vs[i] G b n _ _ _ at h
  rw [atPass] at h
  exact h.fits rfl sel m

end PairSimulation.ShrinkCallCapacity

end VPVNP
end Computability
end OAI
