import OAI.Computability.VPVNP.PairNativeFrameGeometry
import OAI.Computability.VPVNP.PairShrinkCallHeader
import OAI.Computability.VPVNP.PairShrinkCallWorkspace
import OAI.Computability.VPVNP.ShrinkFieldBounds

/-!
# Private capacity of all selected shrinking map calls

The cursor branch bounds every intermediate width by an envelope of order
`n ^ (3/10)`. The fixed block factor multiplying that envelope still gives
at most `n` for all large inputs. Hence a whole admitted supply field,
including its selectors, fits the square stride read by the native handoff.
The map workspace follows the persistent leaf cache and its scalar stacks.
All shared fields, nine staging fields and both selector buffers have a single
polynomial upper address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallCapacity

open Compression Compression.PackingData Compression.ShrinkMotif CompressorRecords
open CursorBounds CursorNetwork MotifBlocks MotifGrid MotifConversion Filter
open NodeArguments ShrinkCallFields
open private shrinkMotif_count from OAI.Computability.VPVNP.PairSimulationSelectorBounds

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {factor : ℝ}

/-- Uniform in the branch and its levels. Absorb a fixed linear width factor
into the live input length before selecting a level or motif. -/
theorem eventually_levels (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        ∀ z : (B.execute f hf T hT X).Choices, ∀ v ∈ executeLevels B f hf T hT X z,
          v.input.positions ≤ initialPositions b n ∧ K * (v.input.maxWireWidth + 1) ≤ n := by
  filter_upwards [eventually_pairBranchBounds B u b hb, eventually_ge_atTop (2 * K * K + 1)]
    with n branch large
  intro base lanes labels hD hT R _ f hf X T z v hv
  obtain ⟨positions, width⟩ := executeLevels_limits B f hf T hT X z v hv
  refine ⟨positions.trans_eq (pairInput_positions S labels hD), ?_⟩
  let L := B.growthConstant ^ T * (X.maxWireWidth + 1)
  have small : (L : ℝ) ≤ (n : ℝ) ^ (3 / 10 : ℝ) := (branch.2.2 labels hD hT R f hf z).2.2.2.2.2.1
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hs : (L : ℝ) ≤ Real.sqrt n := small.trans (by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hn
    norm_num)
  have sq : L * L ≤ n := by
    exact_mod_cast (mul_le_mul hs hs (Nat.cast_nonneg L) (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt (Nat.cast_nonneg n))
  change v.input.maxWireWidth ≤ L at width
  apply (Nat.mul_le_mul_left K (Nat.succ_le_succ width)).trans
  by_cases h : 2 * K ≤ L
  · by_cases hzero : L = 0
    · rw [hzero] at h ⊢
      have hk : K = 0 := by omega
      simp [hk]
    · have hsuc : L + 1 ≤ 2 * L := by omega
      calc
        K * (L + 1) ≤ K * (2 * L) := Nat.mul_le_mul_left _ hsuc
        _ = (2 * K) * L := by ring
        _ ≤ L * L := Nat.mul_le_mul_right _ h
        _ ≤ n := sq
  · calc
      K * (L + 1) ≤ K * (2 * K) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * K * K := by ring
      _ ≤ n := by omega

/-- Reserve four shared words per global motif, nine staging words, the port
directory, the argument descriptor and both selector buffers. -/
def extent (motifs n : ℕ) : ℕ :=
  4 * motifs * n ^ 2 + 9 * n ^ 2 + 16 + Fintype.card Arg + 2 * n

theorem extent_bounded {motifs : ℕ → ℕ} (hM : PolynomiallyBounded motifs) :
    PolynomiallyBounded (fun n ↦ extent (motifs n) n) := by
  have shared := ((PolynomiallyBounded.const 4).mul hM).mul (PolynomiallyBounded.id.pow 2)
  have staged := (PolynomiallyBounded.const 9).mul (PolynomiallyBounded.id.pow 2)
  exact (((shared.add staged).add (.const 16)).add (.const (Fintype.card Arg))).add
    ((PolynomiallyBounded.const 2).mul .id)

/-- Map temporaries start immediately after the persistent cache and all
scalar verifier stacks. The histogram stays in its original interval. -/
def mapBase (R : LeafArena.Regions) (ports n : ℕ) : ℕ := R.stackBase + ports * n ^ 40

theorem histogram_before (R : LeafArena.Regions) (ports n : ℕ) :
    R.histBase + R.histWords ≤ mapBase R ports n :=
  R.hist_before.trans ((Nat.le_add_right R.cacheBase 38).trans (Nat.le_add_right _ _))

variable {a g : ℕ} (X : State a (packingLaneBits a g))
variable (F : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

variable (sel : X.ShrinkSelection F) (m : X.packingData.Motif)
local notation "demand" => X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m
local notation "payload" => Subtype.val (sel m)
local notation "copies" => repetitions F (demand)
local notation "ord" => Fin.val (ShrinkMotifOrder.stateNumber X m)

/-- The square stride also suffices using only the coarse input width bound
`X.maxWireWidth ≤ n`. The finer cursor estimate in `eventually_levels`
puts the copy count below `n` itself. -/
theorem square_widths {n : ℕ} (hn : 1 ≤ n) (wide : 2 * fieldFactor F ≤ n)
    (hw : X.maxWireWidth ≤ n) :
    (∀ e, (demand) e ≤ n ^ 2) ∧ copies ≤ 2 * fieldFactor F * n ∧
      copies ≤ n ^ 2 ∧ ∀ e, (payload) e + copies * F.selectorBits ≤ n ^ 2 := by
  have bound := X.packingData.shrinkTerm_bounds (State.two_le_packingColors _)
    (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth (fun _ ↦ X.width_le_maxWireWidth _)
    F m (sel m)
  have field : fieldFactor F * (X.maxWireWidth + 1) ≤ 2 * fieldFactor F * n := by
    calc
      _ ≤ fieldFactor F * (2 * n) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have sq : 2 * fieldFactor F * n ≤ n ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ wide
  have lo : n ≤ n ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right n hn
  refine ⟨fun e ↦ ?_, bound.1.trans field, bound.1.trans (field.trans sq),
    fun e ↦ ((bound.2 e).2.trans field).trans sq⟩
  exact (X.packingData.shrinkDemandWidths_le (State.two_le_packingColors _)
    (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth (fun _ ↦ X.width_le_maxWireWidth _) m e).trans
      (hw.trans lo)

/-- The CD base at C or D points to the complete genuine input half-field.
Its end remains below hidden storage whenever the child packet does. -/
theorem cd_end (A : Arena) (older pitch hidden : ℕ)
    (below : ∀ v (z : X.network.Half v),
      A.base (older + pitch * PortRefresh.ArgumentAddress.siteOrdinal X v) +
        (packed X v z).length ≤ hidden) (dir : Bool) :
    ShrinkCallHeader.cdBase X m A older pitch dir + (demand) true ≤ hidden := by
  let d := if dir then !(ShrinkOldHalves.cDirection X m) else ShrinkOldHalves.cDirection X m
  let v := X.packingInputIso.site (ShrinkOldHalves.position X m.val d)
  let j := ShrinkOldHalves.slot X m.val d
  let z : X.network.Half v := ⟨fun _ _ _ ↦ false, fun _ _ _ ↦ false⟩
  have len := congrArg List.length (ShrinkOldHalves.slot_bits X m.val d z)
  have hw : X.halfWidth v d j = X.packingWidth m.val := by simpa only [List.length_ofFn] using len
  change A.fieldAddress X v (older + pitch * PortRefresh.ArgumentAddress.siteOrdinal X v) d j +
    X.packingWidth m.val ≤ hidden
  rw [← hw]
  exact (field_end_le X v z A _ d j).trans (below v z)

/-- Numerical sufficiency for the actual native square stride. Both halves
of the demand and every admitted selector-augmented supply field are bounded
uniformly before the row ordinal is supplied. -/
theorem fits {b n labels hist work bound motifs : ℕ} (hn : 1 ≤ n) (histLe : hist + labels ≤ work)
    (workLe : work ≤ bound)
    (motifLe : ShrinkTermInputs.motifCount X ≤ motifs)
    (width : (fieldFactor F + 1) * (X.maxWireWidth + 1) ≤ n)
    (cap : MapWorkspace.Capacity F (wordBits b n) n (bound + extent motifs n))
    (A : Arena) (older pitch : ℕ)
    (below : ∀ v (z : X.network.Half v),
      A.base (older + pitch * PortRefresh.ArgumentAddress.siteOrdinal X v) +
        (packed X v z).length ≤ work) :
    let scratch := ShrinkCallHeader.scratch X work (n ^ 2) hist
    Fits (w := wordBits b n) (n := n) (limit := bound + extent motifs n)
      (u := copies) (t := labels) F (demand) (payload) scratch ord
      (ShrinkCallHeader.cdBase X m A older pitch) := by
  intro s
  have term := X.packingData.shrinkTerm_bounds (State.two_le_packingColors _)
    (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth (fun _ ↦ X.width_le_maxWireWidth _)
    F m (sel m)
  have ab := X.packingData.shrinkDemandWidths_le (State.two_le_packingColors _)
    (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth (fun _ ↦ X.width_le_maxWireWidth _) m false
  rw [Nat.add_mul, Nat.one_mul] at width
  have all : fieldFactor F * (X.maxWireWidth + 1) ≤ n := by omega
  have hcopy : copies ≤ n := term.1.trans all
  have sq : n ≤ n ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ hn
  have card := Fintype.card_congr (ShrinkMotifOrder.stateNumber X)
  rw [Fintype.card_fin] at card
  have idx : ord < s.motifs := by
    change ord < Fintype.card X.packingData.Motif
    rw [card]
    exact (ShrinkMotifOrder.stateNumber X m).isLt
  refine ⟨cap, hcopy, idx, ab.trans (by change _ ≤ n ^ 2; omega),
    cd_end X m A older pitch _ below, fun e ↦ ((term.2 e).2.trans all).trans sq, ?_, ?_⟩
  · dsimp [s, ShrinkCallHeader.scratch, Scratch.directory, Scratch.staging]
    omega
  · have hM : 4 * ShrinkTermInputs.motifCount X * n ^ 2 ≤ 4 * motifs * n ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ motifLe)
    dsimp [s, ShrinkCallHeader.scratch, Scratch.target, Scratch.source, Scratch.descriptor,
      Scratch.directory, Scratch.staging, extent]
    omega

/-- The threshold precedes every selection and every workspace address.
An arbitrary polynomial upper bound on the end of the leaf stacks suffices. -/
theorem eventually_capacity (b : ℕ) (hb : 1 ≤ b) (degree : ℕ) {work : ℕ → ℕ}
    (hW : PolynomiallyBounded work) :
    ∀ᶠ n : ℕ in atTop, MapWorkspace.Capacity F (wordBits b n) n
      (work n + extent (initialPositions b n * degree) n) :=
  MapWorkspace.eventually_capacity (B := F) b hb _
    (hW.add (extent_bounded ((CursorRAM.bounded_positions b).mul (.const degree))))

/-- All admitted motif IDs fit the global reservation, including those in
subsequent shrinks whose base and remaining lane counts have changed. -/
theorem motif_count {b n degree : ℕ} (positions : X.positions ≤ initialPositions b n)
    (slots : 2 ^ a ≤ degree) : ShrinkTermInputs.motifCount X ≤ initialPositions b n * degree :=
  (shrinkMotif_count X).trans (Nat.mul_le_mul positions slots)

open Classical in
/-- On the actual terminal layout the child row-number bound puts its entire
packet below the histogram. Hidden and staged supply fields use the square
stride in their dedicated region above the scalar stacks. -/
theorem eventually_terminal_fits (b degree labels ports : ℕ) (hb : 1 ≤ b) {workLimit : ℕ → ℕ}
    (hW : PolynomiallyBounded workLimit) :
    ∀ᶠ n : ℕ in atTop, ∀ {a g : ℕ} (X : State a (packingLaneBits a g))
      (sel : X.ShrinkSelection F) (m : X.packingData.Motif)
      (firstRow rowWords older pitch : ℕ),
      let G := NativeFrame.regions degree n firstRow rowWords labels
      let scratch := ShrinkCallHeader.scratch X (mapBase G ports n) (n * n) G.histBase
      let sizes := X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m
      mapBase G ports n ≤ workLimit n → 2 ^ a ≤ degree → X.positions ≤ initialPositions b n →
      (fieldFactor F + 1) * (X.maxWireWidth + 1) ≤ n →
      (∀ v : X.network.Site,
        older + pitch * PortRefresh.ArgumentAddress.siteOrdinal X v < G.nodes) →
      Fits (w := wordBits b n) (n := n) (u := repetitions F sizes) (t := labels)
        (limit := workLimit n + extent (initialPositions b n * degree) n)
        F sizes (sel m).val scratch (ShrinkMotifOrder.stateNumber X m).val
          (ShrinkCallHeader.cdBase X m G.arguments older pitch) := by
  filter_upwards [eventually_capacity F b hb degree hW, eventually_ge_atTop 1]
    with n cap hn
  intro a g X sel m firstRow rowWords older pitch G scratch sizes workFit hd pos width nodes
  have hw : X.maxWireWidth ≤ n := by
    rw [Nat.add_mul, Nat.one_mul] at width
    omega
  have hist : G.histBase + labels ≤ mapBase G ports n := histogram_before G ports n
  have packet (v : X.network.Site) (z : X.network.Half v) :
      G.arguments.base (older + pitch * PortRefresh.ArgumentAddress.siteOrdinal X v) +
        (packed X v z).length ≤ mapBase G ports n := by
    have len : (packed X v z).length ≤ G.arguments.stride :=
      (packed_length_le X v z).trans ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 hd) hw).trans
        (Nat.le_succ _))
    have before := G.node_before (nodes v)
    exact (Nat.add_le_add_left len _).trans (before.trans (by omega))
  simpa only [scratch, sizes, pow_two] using
    fits X F sel m hn hist workFit (motif_count X pos hd) width cap G.arguments older pitch packet

end PairSimulation.ShrinkCallCapacity

end VPVNP
end Computability
end OAI
