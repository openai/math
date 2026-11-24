import OAI.Computability.VPVNP.PairTerminalLayout
import OAI.Computability.VPVNP.PairTraversalArena
import OAI.Computability.VPVNP.PairTerminalPrefixLayout
import OAI.Computability.VPVNP.PairSimulationFinalBitScan

/-!
# The shared-bit worker on the selected terminal layout

The high header is beyond the stored row, wire and role intervals on every
selected branch. The tag and row writers preserve that header. After the
shared choices, its contents and the stored descriptor rows remain available
to each vertex, while both endpoints of each wire read the same chosen bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLayout

open BurstRAM BurstRAM.PrivateRAM Compression CursorNetwork CursorBounds CompressorRecords
open Filter TraversalRows TraversalRoles
open scoped Fin.CommRing

private theorem address_lt_word (b n : ℕ) : addressBits b n < wordBits b n :=
  (by omega : addressBits b n < addressBits b n+10).trans_le
    (Nat.le_self_pow (by decide : 4 ≠ 0) _)

/-- The two arrays used to assemble the descriptor arena preserve every
external header or control word above the last role. -/
theorem arena_above {w : ℕ} (cap base F : ℕ) (roles : List TaggedLayer) (m : Memory w)
    (x : ℕ) (h : base + 2 * tagWords cap roles + F ≤ x) :
    build cap base base (roles.map TaggedLayer.layer)
      (writeTags (tagWords cap roles+F) cap base roles m) x = m x := by
  rw [build_outside _ _ _ _ _ _ (Or.inr (by change base+tagWords cap roles ≤ x; omega)),
    write_tags_outside _ _ _ _ _ _ (Or.inr (by omega))]

/-- Actual live header words and the selected final width suffice for the
physical shared-bit scan. Its numerical range is derived at the uniform
threshold, including the controller's two saved cells. -/
theorem eventually_sharedBits {k : Type*} [_root_.Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (F : DescriptorSpace.Shape)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) {start : ℕ → ℕ} (hstart : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let w := wordBits b n
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute f hf T hT X
      let L := DescriptorSpace.cursorLayout F b S.steps u.θ (start n) n
      let rowBase := DescriptorSpace.endAddress L
      ∀ (z : E.Choices) (pub : Fin 11 → Word w),
        let Y := E.finalState z
        let rows := words B.recordLimit (selectedLayers B f hf T hT X z)
        let lo := rowBase+rows
        let H := (TerminalLink.header pub).val
        (pub 2).val = start n → (pub 7).val = addressBits b n →
        lo + Y.totalWidth < H ∧ H + 32 ≤ 2^w ∧
        ∀ (m : Memory w), FinalBits.Worker.base pub m = (lo : Word w) →
          FinalBits.Worker.total pub m = (Y.totalWidth : Word w) →
          FinalBits.Worker.Layout pub m lo Y.totalWidth := by
  filter_upwards [eventually_fit B u F b hb hstart 0] with n fit
  intro base lanes labels hD hT A _ f hf w X T E L rowBase z pub Y rows lo H ws exponent
  have bound := fit labels hD hT A f hf z
  change rowBase + 2*rows + Y.totalWidth < headerBase (start n) (addressBits b n) ∧
    headerBase (start n) (addressBits b n)+32 ≤ 2^w ∧ _ at bound
  let r := addressBits b n
  have reserve : 32 ≤ L.base+2^r*2^r := by
    have pos := bound.1
    change rowBase+2*rows+Y.totalWidth < L.base + (2^r)^2 - 32 at pos
    rw [pow_two] at pos
    omega
  have room : L.base+2^r*2^r ≤ 2^w := by
    have h := bound.2.1
    change L.base+(2^r)^2-32+32 ≤ 2^w at h
    rwa [pow_two, Nat.sub_add_cancel reserve] at h
  have hdr := TerminalPrefix.header_val L pub r ws exponent (address_lt_word b n) reserve room
  change H = L.base + 2^r*2^r - 32 at hdr
  have heq : H = headerBase (start n) (addressBits b n) := by
    change H = L.base + (2^r)^2 - 32
    rw [pow_two]
    exact hdr
  have below : lo+Y.totalWidth < H := by
    rw [heq]
    dsimp only [lo]
    omega
  have hroom : H+32 ≤ 2^w := heq ▸ bound.2.1
  exact ⟨below,hroom,fun _ hb ht => FinalBits.Worker.Layout.ofBelow hb ht below.le hroom⟩

end PairSimulation.TerminalLayout

end VPVNP
end Computability
end OAI
