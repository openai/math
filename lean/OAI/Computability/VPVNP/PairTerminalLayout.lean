import OAI.Computability.VPVNP.PairSimulationLeafArena
import OAI.Computability.VPVNP.PairSimulationNodeFieldSpace
import OAI.Computability.VPVNP.PairTraversalRows
import OAI.Computability.VPVNP.CompressorDescriptorSquare

/-!
# Physical terminal layout of the compressed pair

The final 32 words of the live pair workspace hold the terminal controller
header. The selected traversal rows, final bit interval and role words lie
below it. A private burst uses a node's absolute descriptor address for its
argument buffer. The first unused node buffer begins the private histogram.
A twelve-word geometry directory follows that histogram, and a 38-word
operand cache precedes the local verifier stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLayout

open Compression CursorBounds CursorNetwork CompressorRecords Filter TraversalRows

/-- Beginning of the terminal controller header inside the live pair workspace. -/
def headerBase (workspace r : ℕ) : ℕ := workspace + (2 ^ r)^2 - 32

/-- The program-wide argument, histogram, cache and stack intervals. -/
def privateRegions (degree n rowEnd labelCount : ℕ) : LeafArena.Regions :=
  ⟨⟨n, NodeArguments.frameStride degree n⟩, rowEnd, labelCount, n^5⟩

/-- Immutable words reloaded by cursor leaves and the map dispatch after
the DFS has popped their node address. Cell `n` points at this array. -/
def geometry (R : LeafArena.Regions)
    (rowBase rowStride radixB radixL shadow span roleOffset n : ℕ) :
    Fin 12 → ℕ :=
  ![rowBase,rowStride,radixB,radixL,shadow,span,R.arguments.start,R.arguments.stride,
    R.cacheBase,n,roleOffset,R.histBase]

theorem regions_formulas (degree n rowEnd labels : ℕ) :
    let R := privateRegions degree n rowEnd labels
    R.histBase = n + rowEnd * (2 * degree * n + 1) ∧
    R.cacheBase = R.histBase + labels + n^5 ∧ R.stackBase = R.cacheBase + 38 := ⟨rfl,rfl,rfl⟩

private theorem positiveEnd (L : DescriptorSpace.Layout) : 0 < DescriptorSpace.endAddress L := by
  rw [DescriptorSpace.endAddress_eq, DescriptorSpace.Shape.fixedWords]
  omega

/-- Every real node buffer starts above the private cell that points to
the immutable geometry. This includes the initial cursor layer. -/
theorem geometryPointer_before_node {n degree rowEnd labels node : ℕ}
    (L : DescriptorSpace.Layout) (h : DescriptorSpace.endAddress L ≤ node) :
    n < (privateRegions degree n rowEnd labels).arguments.base node := by
  have hn := (positiveEnd L).trans_le h
  change n < n + node*(2*degree*n+1)
  exact Nat.lt_add_of_pos_right (Nat.mul_pos hn (Nat.succ_pos _))

/-- All simultaneous external and private regions fit on every selected
cursor branch. The untouched high header and the private pointer cell are
separated from their adjacent live arrays. -/
theorem eventually_fitWithReserve {k : Type*} [_root_.Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (F : DescriptorSpace.Shape)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) {start : ℕ → ℕ} (hstart : PolynomiallyBounded start)
    (ports : ℕ) (extra : ℕ → ℕ) (hextra : PolynomiallyBounded extra) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute f hf T hT X
      let L := DescriptorSpace.cursorLayout F b S.steps u.θ (start n) n
      let rowBase := DescriptorSpace.endAddress L
      let H := headerBase (start n) (addressBits b n)
      ∀ z : E.Choices,
        let Y := E.finalState z
        let rows := words B.recordLimit (selectedLayers B f hf T hT X z)
        let R := privateRegions (slotDegree S) n (rowBase+rows) (Fintype.card B.Entry)
        rowBase + 2*rows + Y.totalWidth < H ∧ H + 32 ≤ 2^(wordBits b n) ∧
          R.histBase + R.histWords + 12 ≤ R.cacheBase ∧
          R.stackBase + ports*n^40 + extra n < 2^(wordBits b n) := by
  let K := 2*(B.recordLimit+2)+33
  let P := initialPositions b
  let maxEnd n := start n + (P n)^2
  let maxPrivate n := (privateRegions (slotDegree S) n (maxEnd n) (Fintype.card B.Entry)).stackBase
    + ports*n^40 + extra n
  have hmax : PolynomiallyBounded maxEnd := hstart.add ((CursorRAM.bounded_positions b).pow 2)
  have hprivate : PolynomiallyBounded maxPrivate := by
    dsimp only [maxPrivate, privateRegions, LeafArena.Regions.stackBase,
      LeafArena.Regions.cacheBase, LeafArena.Regions.histBase, NodeArguments.Arena.base]
    have frame := PolynomiallyBounded.id.add
      (hmax.mul (NodeArguments.frameStride_bounded (slotDegree S)))
    have hist := frame.add (PolynomiallyBounded.const (Fintype.card B.Entry))
    have cache := hist.add (PolynomiallyBounded.id.pow 5)
    exact ((cache.add (PolynomiallyBounded.const 38)).add
      ((PolynomiallyBounded.const ports).mul (PolynomiallyBounded.id.pow 40))).add hextra
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  filter_upwards [DescriptorSpace.eventually_selected_square F B u b hb K,
    CursorRAM.eventual_word_room b hb' hmax, CursorRAM.eventual_word_room b hb' hprivate,
    eventually_ge_atTop 3] with n hs hmax hprivate hn
  intro base lanes labels hD hT A _ f hf X T E L rowBase H z Y rows R
  have foot := selected_words_le B f hf T hT X z
  change rows ≤ (B.recordLimit+2)*Y.positions*B.growthConstant^T at foot
  have square := hs (start n) labels hD hT A f hf z
  have far : rowBase + 2*rows + Y.totalWidth + 32 < start n + (processorCount b n)^2 := by
    apply lt_of_le_of_lt _ square
    change rowBase+2*rows+Y.totalWidth+32 ≤
      rowBase+K*(X.positions+processorCount b n+Y.positions*B.growthConstant^T+Y.totalWidth)+1
    have hp := X.positions_pos
    dsimp only [K]
    nlinarith only [foot, hp,
      Nat.zero_le (B.recordLimit*(X.positions+processorCount b n+Y.totalWidth))]
  have hR : processorCount b n ≤ P n :=
    (Nat.pow_le_pow_right Nat.zero_lt_two (addressBits_le_virtualBits b n hn)).trans
      (Nat.le_mul_of_pos_right _ (by omega : 0 < virtualBits b n))
  have hEnd : start n + (processorCount b n)^2 ≤ maxEnd n := Nat.add_le_add_left
    (Nat.pow_le_pow_left hR 2) _
  have hpos : rowBase+rows ≤ maxEnd n := (by omega :
      rowBase+rows ≤ start n + (processorCount b n)^2).trans hEnd
  change rowBase+2*rows+Y.totalWidth < start n+(processorCount b n)^2-32 ∧
    start n+(processorCount b n)^2-32+32 ≤ 2^(wordBits b n) ∧ _ ∧ _
  refine ⟨by omega, (by omega : _ ≤ start n+(processorCount b n)^2).trans (hEnd.trans hmax.le),
    ?_, ?_⟩
  · change R.histBase + Fintype.card B.Entry + 12 ≤ R.histBase + Fintype.card B.Entry + n^5
    exact Nat.add_le_add_left ((by decide : 12 ≤ 3^5).trans (Nat.pow_le_pow_left hn 5)) _
  · apply lt_of_le_of_lt _ hprivate
    dsimp only [maxPrivate, R, privateRegions, LeafArena.Regions.stackBase,
      LeafArena.Regions.cacheBase, LeafArena.Regions.histBase, NodeArguments.Arena.base]
    gcongr

/-- The selected private region through the last virtual verifier stack. -/
theorem eventually_fit {k : Type*} [_root_.Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (F : DescriptorSpace.Shape)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) {start : ℕ → ℕ} (hstart : PolynomiallyBounded start)
    (ports : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute f hf T hT X
      let L := DescriptorSpace.cursorLayout F b S.steps u.θ (start n) n
      let rowBase := DescriptorSpace.endAddress L
      let H := headerBase (start n) (addressBits b n)
      ∀ z : E.Choices,
        let Y := E.finalState z
        let rows := words B.recordLimit (selectedLayers B f hf T hT X z)
        let R := privateRegions (slotDegree S) n (rowBase+rows) (Fintype.card B.Entry)
        rowBase + 2*rows + Y.totalWidth < H ∧ H + 32 ≤ 2^(wordBits b n) ∧
          R.histBase + R.histWords + 12 ≤ R.cacheBase ∧
          R.stackBase + ports*n^40 < 2^(wordBits b n) := by
  simpa only [Nat.add_zero] using
    eventually_fitWithReserve B u F b hb hstart ports (fun _ => 0) (PolynomiallyBounded.const 0)

end PairSimulation.TerminalLayout

end VPVNP
end Computability
end OAI
