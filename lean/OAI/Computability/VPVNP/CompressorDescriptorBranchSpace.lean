import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorLevelCounts
import OAI.Computability.VPVNP.CursorBranchBudget

/-!
# Descriptor capacity on actual compressor branches

Each substep on the selected cursor execution fits the level and slot ranges
of Appendix E. The final wire bits and the DFS row arena fit after the last
descriptor array, with one threshold for every coefficient specialization
and admissible branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorSpace

open Compression CursorBounds CursorNetwork Filter
variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- The reserved levels, site rows, and slot rows cover every substep of
the genuine selected compressor execution, including both endpoint graphs
of the substep and all of its motifs. -/
theorem selected_level_capacity (L : Layout) (B : S.Templates) {A : Type*} [CommRing A]
    (f : B.Entry → A) (hf : B.IsSolution f) {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)
    (hsteps : (S.steps + 1) * T < L.levels) (hpos : X.positions ≤ L.positions)
    (hslots : slotDegree S ≤ L.shape.slots) :
    (executeLevels B f hf T hT X z).length < L.levels ∧
      ∀ v ∈ executeLevels B f hf T hT X z,
        v.input.positions ≤ L.positions ∧ v.outputSites ≤ L.positions ∧
        v.oldSlots ≤ slotCapacity L ∧ v.outputSlots ≤ slotCapacity L ∧
        v.origin.motifCount ≤ slotCapacity L := by
  refine ⟨(executeLevels_length B f hf T hT X z).trans_lt hsteps, fun v hv ↦ ?_⟩
  have hin := ((executeLevels_limits B f hf T hT X z v hv).1).trans hpos
  have hout := v.outputSites_le.trans hin
  have hold := Nat.mul_le_mul hin (v.oldDegree_le.trans hslots)
  exact ⟨hin, hout, hold, Nat.mul_le_mul hout (v.outputDegree_le.trans hslots),
    v.origin.motifCount_le.trans hold⟩

/-- After all descriptor arrays there is room for the selected final wires,
the DFS row arena and an additional polynomial suffix. The length threshold
precedes the coordinate split, specialization, and branch choice. -/
theorem eventually_selected_room (F : Shape) (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) {start suffix : ℕ → ℕ}
    (hstart : PolynomiallyBounded start) (hsuffix : PolynomiallyBounded suffix) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let T := blockCount (u.θ : ℝ) n
        let X := pairInput S labels hD
        let E := B.execute f hf T hT X
        let L := cursorLayout F b S.steps (u.θ : ℝ) (start n) n
        ∀ z : E.Choices, let Y := E.finalState z
          endAddress L + Y.totalWidth + (B.recordLimit + 2) * Y.positions * B.growthConstant ^ T +
            suffix n < 2 ^ wordBits b n := by
  have hθ : (u.θ : ℝ) ≤ 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
    norm_num at this
    linarith only [this]
  let K := B.recordLimit + 2
  let P := initialPositions b
  let cap n := endAddress (cursorLayout F b S.steps (u.θ : ℝ) (start n) n) +
    P n * n + K * (P n * n) + suffix n
  have hp := CursorRAM.bounded_positions b
  have hc : PolynomiallyBounded cap :=
    (((bounded_cursorEnd F b S.steps hθ hstart).add (hp.mul PolynomiallyBounded.id)).add
      ((PolynomiallyBounded.const K).mul (hp.mul PolynomiallyBounded.id))).add hsuffix
  have hb' := (le_max_right S.laneBits 5).trans hb
  filter_upwards [CursorRAM.eventual_word_room b (by omega) hc,
    eventually_pairBranchBounds B u b hb, eventually_ge_atTop 3] with n hroom branch hn
  intro base lanes labels hD hT A _ f hf T X E L z Y
  have bounds := branch.2.2 labels hD hT A f hf z
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hproc : processorCount b n ≤ P n := by
    apply (Nat.pow_le_pow_right Nat.zero_lt_two (addressBits_le_virtualBits b n hn)).trans
    exact Nat.le_mul_of_pos_right _ (zero_lt_one.trans hD)
  have hwidth : Y.totalWidth ≤ P n * n := by
    have ht := bounds.2.1
    change (Y.totalWidth : ℝ) ≤ (processorCount b n : ℝ) * (n : ℝ) ^ (1 - u.θ / 2 : ℝ) at ht
    have he : (1 - (u.θ : ℝ) / 2 : ℝ) ≤ 1 := by
      have hpθ := (Rat.cast_pos (K := ℝ)).mpr u.theta_pos
      linarith only [hpθ]
    have hpow : (n : ℝ) ^ (1 - u.θ / 2 : ℝ) ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn₁ he
    apply Nat.cast_le (α := ℝ) |>.mp
    rw [Nat.cast_mul]
    exact ht.trans (mul_le_mul (Nat.cast_le.mpr hproc) hpow
      (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Nat.cast_nonneg _))
  have hhist : B.growthConstant ^ T ≤ n := by
    have hfield := bounds.2.2.2.2.2.1
    change ((B.growthConstant ^ T * (X.maxWireWidth + 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ (3/10 : ℝ) at hfield
    have hpow : (n : ℝ) ^ (3/10 : ℝ) ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (3/10 : ℝ) ≤ 1)
    have : B.growthConstant ^ T * (X.maxWireWidth + 1) ≤ n := Nat.cast_le (α := ℝ) |>.mp (hfield.trans hpow)
    exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans this
  have hy : Y.positions ≤ P n := bounds.1
  have hdfs := Nat.mul_le_mul_left K (Nat.mul_le_mul hy hhist)
  apply lt_of_le_of_lt _ hroom
  change endAddress L + Y.totalWidth + K * Y.positions * B.growthConstant ^ T + suffix n ≤
    endAddress L + P n * n + K * (P n * n) + suffix n
  rw [Nat.mul_assoc]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hwidth _) hdfs) _

end CompressorRecords.DescriptorSpace

end VPVNP
end Computability
end OAI
