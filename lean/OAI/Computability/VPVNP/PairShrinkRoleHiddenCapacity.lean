import OAI.Computability.VPVNP.PairShrinkRolePackedHidden
import OAI.Computability.VPVNP.PairShrinkPackedCapacity

/-!
# Uniform capacity of the hidden fields at the selected shrinking sites

The packed directory and the post-stack reservation suffice for the actual
zero seed at every output site, for all selected branches beyond one length
threshold. No field values or coefficient assignments enter the threshold.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.PackedHidden

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords DescriptorSpace
open ShrinkBlockInputs ShrinkHistoryRows ShrinkCallCapacity CursorBounds CursorNetwork
open TraversalRows Filter LocalHistory

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  (u : PairExponents B.growthConstant) (b₀ : ℕ) (hb : max S.laneBits 5 ≤ b₀)
  {start : ℕ → ℕ} (hs : PolynomiallyBounded start)

local notation "P" => initialPositions b₀
local notation "T" => blockCount (u.θ : ℝ)
local notation "degree" => slotDegree S

include hs hb in
/-- All header, term, count, row and private-slot facts for any chosen shrinking
occurrence and any of its packed sites. -/
theorem eventually_hidden :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b₀ n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b₀ n)
      (hT : T n * S.laneBits ≤ lanes) (A : Type*) [CommRing A]
      (f : B.Entry → A) (hf : B.IsSolution f),
      let initial := pairInput S labels hD
      let firstRow := endAddress (BlockProgram.layout B (start n) (P n) (T n))
      let w := wordBits b₀ n
      ∀ z : (B.execute f hf (T n) hT initial).Choices,
        let vs := executeLevels B f hf (T n) hT initial z
        let rows := words B.recordLimit (selectedLayers B f hf (T n) hT initial z)
        let R := NativeFrame.regions degree n firstRow rows (Fintype.card B.Entry)
        ∀ (j : Fin vs.length) (i : Fin S.steps) {g : ℕ}
          (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
          (bs : List Bool), vs[j] = shrinkLevel B f hf i X sel bs →
          ∀ (word : Word w) (m : Memory w),
            CompiledResident.ShrinkPayload B word (P n) (T n) n j.val i X sel m →
            ∀ v : MapResidentRows.Site X, Facts B i X sel word (P n) (T n) j.val n R v m := by
  classical
  have hb₁ : 1 ≤ b₀ := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  filter_upwards [eventually_packed_handoff B u b₀ hb hs,
    eventually_levels B u b₀ hb (fieldFactor B.shrink),
    CursorRAM.eventual_word_room b₀ hb₁ (PolynomiallyBounded.const B.shrink.selectorBits),
    eventually_ge_atTop 1] with n handoff size selectorRoom hn
  intro base lanes labels hD hT A _ f hf initial firstRow w z vs rows R j i g X sel bs atPass
    word m payload v
  obtain ⟨pos, wide⟩ := size labels hD hT A f hf z vs[j] (List.getElem_mem j.isLt)
  change vs[j].input.positions ≤ P n at pos
  change fieldFactor B.shrink * (vs[j].input.maxWireWidth + 1) ≤ n at wide
  rw [atPass] at pos wide
  have count := motif_count X pos (shrinkLevel B f hf i X sel bs).oldDegree_le
  have bound := (handoff labels hD hT A f hf z).1
  apply of_payload B i X sel word (P n) (T n) j.val n R v m payload selectorRoom
  · intro motif t
    have h := X.packingData.shrinkTerm_bounds (State.two_le_packingColors _)
      (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth (fun _ => X.width_le_maxWireWidth _)
      B.shrink motif (sel motif)
    exact ((h.2 _).2.trans wide).trans (Nat.le_mul_of_pos_right _ hn)
  · have occupied : (hiddenOrder X).length * (n * n) ≤ 4 * (P n * degree) * n ^ 2 := by
      change (ShrinkTermInputs.motifCount X * 4) * (n * n) ≤ _
      rw [Nat.mul_comm (ShrinkTermInputs.motifCount X) 4, pow_two]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 count)
    apply lt_of_le_of_lt (Nat.add_le_add_left (occupied.trans ?_) _) bound
    unfold extent
    omega

end PairSimulation.ShrinkRole.PackedHidden

end VPVNP
end Computability
end OAI
