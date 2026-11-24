import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory
import OAI.Computability.VPVNP.PairShrinkCallCapacity
import OAI.Computability.VPVNP.PairTerminalPackedBudget

/-! # Word and wire bounds for the children of a packed shrinking pass -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.PackedChildren

open Compression CompressorRecords CursorBounds CursorNetwork DescriptorSpace Filter TraversalRows

/-- One input-length threshold fits the twelve geometry words and every selected
shrinking input's wire widths, uniformly in the specialization and branch. -/
theorem eventually_geometry {k : Type} [_root_.Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (b : ℕ)
    (hb : max S.laneBits 5 ≤ b) {start : ℕ → ℕ} (hstart : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      let L := BlockProgram.layout B (start n) X.positions T
      ∀ z : (B.execute f hf T hT X).Choices,
        let passes := executeLevels B f hf T hT X z
        let rows := words B.recordLimit (selectedLayers B f hf T hT X z)
        let regions := TerminalLayout.privateRegions (slotDegree S) n
          (endAddress L + rows) (Fintype.card B.Entry)
        ∀ (j : Fin passes.length) (i : Fin S.steps) {g : ℕ}
          (Z : State (S.degreeExponent i.castSucc)
            (packingLaneBits (S.degreeExponent i.castSucc) g))
          (sel : SelectedScore.Selection B Z) (bits : List Bool),
          passes[j] = shrinkLevel B f hf i Z sel bits →
            Z.maxWireWidth ≤ n ∧ NativeFrame.frameBase regions + 12 ≤ 2 ^ wordBits b n := by
  filter_upwards [ShrinkCallCapacity.eventually_levels B u b hb 1,
    TerminalLayout.eventually_packedFit B u b hb hstart 0 (fun _ ↦ 0)
      (PolynomiallyBounded.const 0)] with n levels fit
  intro base lanes labels hD hT A _ f hf X T L z passes rows regions j i g Z sel bits atPass
  have width := (levels labels hD hT A f hf z passes[j] (List.getElem_mem j.isLt)).2
  rw [atPass, Nat.one_mul] at width
  refine ⟨(Nat.le_succ Z.maxWireWidth).trans width, ?_⟩
  have packed := fit labels hD hT A f hf z
  have positions : X.positions = initialPositions b n := pairInput_positions S labels hD
  dsimp only [regions, L]
  rw [positions]
  exact (packed.2.2.1.trans (Nat.le_add_right _ 38)).trans (by
    simpa only [Nat.zero_mul, Nat.add_zero, LeafArena.Regions.stackBase] using packed.2.2.2.1.le)

end PairSimulation.ShrinkRole.PackedChildren

end VPVNP
end Computability
end OAI
