import OAI.Computability.VPVNP.PairNativeFrameDescriptor

/-!
# Uniform bound for the native terminal histogram address

The terminal header counts all selected DFS rows, including the final layer. The
private histogram starts after the argument frame for the last possible absolute
row address. A fixed polynomial bounds this address before any branch is chosen.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame

open Compression CursorBounds CursorNetwork CompressorRecords Filter TraversalRows

/-- Reserve one argument frame for each absolute address up to the selected
descriptor space bound. The histogram length does not enter its base address. -/
noncomputable def histLimit (degree b : ℕ) (start : ℕ → ℕ) (n : ℕ) : ℕ :=
  n + (start n + (initialPositions b n)^2) * NodeArguments.frameStride degree n

theorem histLimit_bounded (degree b : ℕ) {start : ℕ → ℕ} (hs : PolynomiallyBounded start) :
    PolynomiallyBounded (histLimit degree b start) :=
  PolynomiallyBounded.id.add ((hs.add ((CursorRAM.bounded_positions b).pow 2)).mul
    (NodeArguments.frameStride_bounded degree))

/-- The polynomial bound holds for every coefficient specialization and all
branches, including at zero compression depth. -/
theorem eventually_selected_histBase {k : Type*} [_root_.Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (F : DescriptorSpace.Shape)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) {start : ℕ → ℕ} (hs : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      let L := DescriptorSpace.cursorLayout F b S.steps u.θ (start n) n
      ∀ z : (B.execute f hf T hT X).Choices,
        let rows := words B.recordLimit (selectedLayers B f hf T hT X z)
        ∀ degree count, (regions degree n (DescriptorSpace.endAddress L) rows count).histBase ≤
          histLimit degree b start n := by
  filter_upwards [TerminalLayout.eventually_fit B u F b hb hs 0,
    eventually_ge_atTop 3] with n selected hn
  intro base lanes labels hD hT A _ f hf X T L z rows degree count
  have below := (selected labels hD hT A f hf z).1
  change DescriptorSpace.endAddress L + 2 * rows + _ <
    start n + (processorCount b n)^2 - 32 at below
  have rowEnd : DescriptorSpace.endAddress L + rows ≤ start n + (processorCount b n)^2 := by omega
  have proc : processorCount b n ≤ initialPositions b n :=
    (Nat.pow_le_pow_right Nat.zero_lt_two (addressBits_le_virtualBits b n hn)).trans
      (Nat.le_mul_of_pos_right _ (by omega : 0 < virtualBits b n))
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _
    (rowEnd.trans (Nat.add_le_add_left (Nat.pow_le_pow_left proc 2) _))) _

/-- Reading the two native header words also respects the bound. Each natural
address encoded in a word can only decrease when reduced modulo the word size. -/
theorem Readback.histBase_le {w firstRow rowWords stride baseRadix laneRadix : ℕ}
    {m : BurstRAM.Memory w} {header span : BurstRAM.Word w}
    (h : Readback m header firstRow rowWords stride baseRadix laneRadix span)
    (degree : ℕ) (pub : Fin 11 → BurstRAM.Word w) :
    (fromHeader degree pub header m).histBase ≤
      (regions degree (pub 6).val firstRow rowWords (pub 9).val).histBase := by
  unfold fromHeader
  rw [h.row, h.words, Fin.val_natCast, Fin.val_natCast]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _
    (Nat.add_le_add (Nat.mod_le _ _) (Nat.mod_le _ _))) _

/-- Uniform upper bound on the first map workspace cell above all native
leaf stacks. Each of the named stack ports reserves `n^40` words. -/
noncomputable def postStackLimit (degree b : ℕ) (start : ℕ → ℕ) (labels ports n : ℕ) :=
  histLimit degree b start n + labels + n^5 + 38 + ports * n^40

theorem postStackLimit_bounded (degree b : ℕ) {start : ℕ → ℕ} (hs : PolynomiallyBounded start)
    (labels ports : ℕ) : PolynomiallyBounded (postStackLimit degree b start labels ports) :=
  let hc := ((histLimit_bounded degree b hs).add (.const labels)).add (PolynomiallyBounded.id.pow 5)
  (hc.add (.const 38)).add ((PolynomiallyBounded.const ports).mul (PolynomiallyBounded.id.pow 40))

theorem postStack_le {degree b n firstRow rowWords labels : ℕ} {start : ℕ → ℕ}
    (ports : ℕ) (hh : (regions degree n firstRow rowWords labels).histBase ≤
      histLimit degree b start n) :
    (regions degree n firstRow rowWords labels).stackBase + ports * n^40 ≤
      postStackLimit degree b start labels ports n :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hh _) _) _)
    _

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
