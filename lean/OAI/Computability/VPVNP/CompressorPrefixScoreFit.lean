import OAI.Computability.VPVNP.CompressorPrefixWorkerFit

/-!
# Both selected layout scores fit at every reachable shrinking state

The bound depends on the number of old sites and the largest old wire.
The selected term may be followed by an empty admissible set at a later
stage. Both score words are already bounded when the term is chosen.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.PrefixLevelScale

open Compression CursorBounds Filter ShrinkMotif
open private shrinkMotif_count from OAI.Computability.VPVNP.PairSimulationSelectorBounds

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

open Classical in
theorem eventually_scores (b : ℕ) (hb : 1 ≤ b) : ∀ᶠ n : ℕ in atTop,
    B.shrink.selectorBits < 2 ^ wordBits b n ∧
    (∀ t : Fin 4, MotifAdmission.weight relativeMass t < 2 ^ wordBits b n) ∧
    ∀ (i : Fin S.steps) {g : ℕ}
      (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g)),
      X.positions ≤ initialPositions b n → X.maxWireWidth ≤ n →
      ∀ (s : SelectedScore.Selection B X) (l : Bool),
        layoutScore relativeMass (X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s)
          l < 2 ^ wordBits b n := by
  let weights := ∑ t : Fin 4, MotifAdmission.weight relativeMass t
  let K := weights * (fieldFactor B.shrink) ^ 2
  let bound n := K * (initialPositions b n * slotDegree S) * (n + 1) ^ 2
  have poly : PolynomiallyBounded bound :=
    ((PolynomiallyBounded.const K).mul ((CursorRAM.bounded_positions b).mul
      (PolynomiallyBounded.const (slotDegree S)))).mul (PolynomiallyBounded.succ.pow 2)
  filter_upwards [CursorRAM.eventual_word_room b hb poly,
    CursorRAM.eventual_word_room b hb (PolynomiallyBounded.const weights),
    CursorRAM.eventual_word_room b hb (PolynomiallyBounded.const B.shrink.selectorBits)]
    with n large weightRoom selector
  refine ⟨selector, fun t ↦ ?_, fun i g X sites width s l ↦ ?_⟩
  · exact (Finset.single_le_sum (f := MotifAdmission.weight relativeMass)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ t)).trans_lt weightRoom
  · have deg : 2 ^ S.degreeExponent i.castSucc ≤ slotDegree S :=
      (Finset.le_sup (f := fun j : Fin (S.steps + 1) ↦ 2 ^ S.degreeExponent j)
        (Finset.mem_univ i.castSucc)).trans (le_max_right _ _)
    have motifs := (shrinkMotif_count X).trans (Nat.mul_le_mul sites deg)
    exact (shrink_layoutScore_le B X s l).trans_lt
      ((Nat.mul_le_mul (Nat.mul_le_mul_left K motifs)
        (Nat.pow_le_pow_left (Nat.succ_le_succ width) 2)).trans_lt large)

end CompressorRecords.PrefixLevelScale

end

end VPVNP
end Computability
end OAI
