import OAI.Computability.VPVNP.CompressorSelectedTerms
import OAI.Computability.VPVNP.CompressorRecordsCursorCapacity
import OAI.Computability.VPVNP.CompressorRecordScores

/-!
# Descriptor arithmetic in the live cursor word format

The chosen field length envelope controls the input to every motif scan.
The two layout scores fit after multiplying the old slot count by the
squared supply width and the fixed denominator-cleared weights. The word
width also gives a uniform polylogarithmic budget for one motif visit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open Compression CursorNetwork CursorBounds Filter PairSimulation.LocalHistory
open scoped Classical

private theorem fieldLimit_le_length {n M : ℕ} (hn : 1 ≤ n) (h : (M : ℝ) ≤ (n : ℝ) ^ (3/10 : ℝ)) :
    M ≤ n := by
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (3/10 : ℝ) ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (3/10 : ℝ) ≤ 1)
  exact_mod_cast h.trans hp

/-- Binary instruction budget per motif visit, including the full payload word scan. -/
theorem word_plus_clog_le (b n M : ℕ) (hM : M ≤ n) :
    wordBits b n + Nat.clog 2 (M+1) + 1 ≤ ((b+10)^4+2)*(n.log2+1)^4 := by
  let L := n.log2+1
  have hb : wordBits b n ≤ ((b+10)*L)^4 := by
    unfold wordBits addressBits BurstRAM.addressWidth
    apply Nat.pow_le_pow_left
    have h := Nat.mul_le_mul_left b (BurstRAM.clog_le_log2_succ n)
    dsimp [L]; nlinarith only [h,Nat.zero_le n.log2]
  have hlog : Nat.clog 2 (M+1) ≤ L := (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr
    ((Nat.succ_le_succ hM).trans Nat.lt_log2_self)
  have hl : 1 ≤ L := Nat.succ_pos _
  have hl4 : L ≤ L^4 := by simpa using (Nat.pow_le_pow_right hl (by decide : 1 ≤ 4))
  have h := Nat.add_le_add (Nat.add_le_add hb (hlog.trans hl4)) (hl.trans hl4)
  apply h.trans_eq
  dsimp only [L]; ring

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- One threshold suffices for every selected substep. The last inequality
holds for any fixed coefficient multiplying the squared intermediate width
and the count of motifs. In particular the cleared-energy counters never wrap. -/
theorem eventually_descriptorWords (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) (K : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
      (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      ∀ z : (B.execute f hf T hT X).Choices, ∀ v ∈ executeLevels B f hf T hT X z,
        SelectedTerms.fitConstant B + 4*Nat.clog 2 (v.input.maxWireWidth+1) ≤ wordBits b n ∧
        wordBits b n + Nat.clog 2 (v.input.maxWireWidth+1) + 1 ≤ ((b+10)^4+2)*(n.log2+1)^4 ∧
        K * v.origin.motifCount * (v.input.maxWireWidth+1)^2 < 2^wordBits b n := by
  have hb' := (le_max_right S.laneBits 5).trans hb
  let cost n := K * (initialPositions b n * slotDegree S) * (n+1)^2
  have hcost : PolynomiallyBounded cost := ((PolynomiallyBounded.const K).mul
    ((CursorRAM.bounded_positions b).mul (PolynomiallyBounded.const (slotDegree S)))).mul (PolynomiallyBounded.succ.pow 2)
  filter_upwards [eventually_pairBranchBounds B u b hb, eventually_ge_atTop 1,
    DemandPreparation.eventually_live_word_fits b (by omega) (SelectedTerms.fitConstant B) 4 1 1,
    CursorRAM.eventual_word_room b (by omega) hcost] with n branch hn fit room
  intro base lanes labels hD hT A _ f hf X T z v hv
  obtain ⟨hp,hw⟩ := executeLevels_limits B f hf T hT X z v hv
  have hwidth := fieldLimit_le_length hn (branch.2.2 labels hD hT A f hf z).2.2.2.2.2.1
  have hm := hw.trans hwidth
  have hx := pairInput_positions S labels hD
  have hmots := v.origin.motifCount_le.trans (Nat.mul_le_mul (hp.trans hx.le) v.oldDegree_le)
  exact ⟨fit _ (by simpa using hm),word_plus_clog_le _ _ _ hm,
    (Nat.mul_le_mul (Nat.mul_le_mul_left K hmots) (Nat.pow_le_pow_left (Nat.succ_le_succ hm) 2)).trans_lt room⟩

/-- The bound consumed by the two native score counters at a genuine
shrinking pass, with payload-plus-selector supply widths on every role. -/
theorem shrink_layoutScore_le (B : S.Templates) {a g : ℕ} (X : State a (packingLaneBits a g))
    (c : ∀ m, X.packingData.ShrinkChoice X.shrinkNumber X.packingWidth B.shrink m) (l : Bool) :
    layoutScore ShrinkMotif.relativeMass
        (fun m l t ↦ X.packingData.shrinkSupplyWidths X.shrinkNumber X.packingWidth B.shrink m (c m) (l,t)) l ≤
      ((∑ t, MotifAdmission.weight ShrinkMotif.relativeMass t) * (ShrinkMotif.fieldFactor B.shrink)^2) *
        (shrinkMotifOrder X).length * (X.maxWireWidth+1)^2 := by
  have hs := layoutScore_le ShrinkMotif.relativeMass
    (fun m l t ↦ X.packingData.shrinkSupplyWidths X.shrinkNumber X.packingWidth B.shrink m (c m) (l,t))
    (ShrinkMotif.fieldFactor B.shrink*(X.maxWireWidth+1))
    (fun m l t ↦ ((X.packingData.shrinkTerm_bounds (State.two_le_packingColors _) (Nat.two_pow_pos _)
      X.shrinkNumber X.packingWidth (fun e ↦ X.width_le_maxWireWidth _) B.shrink m (c m)).2 (l,t)).2) l
  exact hs.trans_eq (by change _ = _ * Fintype.card X.packingData.Motif * _; ring)

end CompressorRecords

end VPVNP
end Computability
end OAI
