import OAI.Computability.VPVNP.IteratedCompression
import OAI.Computability.VPVNP.CursorState
import OAI.Computability.VPVNP.CursorCompressionBudget

/-!
# Budgets of a selected compressed cursor network

Section 12 bounds the shared bits, local records and total number of
history occurrences on each branch. Here the input carries the real
sorting and successor fields of the virtual RAM. The threshold precedes
the lane labeling, coefficient assignment and compressor branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open Compression CursorBounds CursorRouting Filter

variable {k : Type*} [Field k] {S : BlockSchedule k}

/-- Place the virtual RAM at the cursor-zero positions and reserve the
successor and sorting message fields on both physical routing arcs. -/
noncomputable def pairInput (S : BlockSchedule k) {b n base lanes : ℕ}
    (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n) :
    State (S.degreeExponent 0) lanes :=
  cursorState labels hD (Nat.add_sub_of_le S.degree_bounds.1)
    (ramFieldBits (virtualBucket n) (wordBits b n) : RAMSystem (virtualBits b n) → ℕ)

theorem pairInput_positions (S : BlockSchedule k) {b n base lanes : ℕ}
    (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n) :
    (pairInput S labels hD).positions = initialPositions b n :=
  cursorState_positions _ _ _ _

theorem pairInput_maxWireWidth (S : BlockSchedule k) {b n base lanes : ℕ}
    (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n) :
    (pairInput S labels hD).maxWireWidth ≤ initialWidth b n := by
  apply Finset.sup_le
  intro e _
  let bits := (ramFieldBits (virtualBucket n) (wordBits b n) : RAMSystem (virtualBits b n) → ℕ)
  change paddedWidth bits ((stateEdges labels (Nat.add_sub_of_le S.degree_bounds.1)).symm
    ((e.1.1,e.2),e.1.2)) ≤ initialWidth b n
  cases (stateEdges labels (Nat.add_sub_of_le S.degree_bounds.1)).symm ((e.1.1,e.2),e.1.2) with
  | inl => exact le_rfl
  | inr => exact Nat.zero_le _

theorem pairInput_sqrtEnergy (S : BlockSchedule k) {b n base lanes : ℕ}
    (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n) :
    Real.sqrt (pairInput S labels hD).energy ≤
      (initialPositions b n : ℝ) * S.baseDegree * initialWidth b n := by
  have hpad : 2 + (2 ^ S.degreeExponent 0 - 2) = S.baseDegree := Nat.add_sub_of_le S.degree_bounds.1
  unfold pairInput initialWidth initialPositions
  simpa only [hpad] using
    (cursorState_sqrtEnergy_le labels hD (Nat.add_sub_of_le S.degree_bounds.1)
      (ramFieldBits (virtualBucket n) (wordBits b n) : RAMSystem (virtualBits b n) → ℕ))

private theorem eventually_widthEnvelope (b d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop,
      ((initialPositions b n : ℝ) * d * initialWidth b n + A * initialPositions b n) /
        2 ^ blockCount θ n ≤ (processorCount b n : ℝ) * (n : ℝ) ^ (1 - θ/2) := by
  let p := 2 * ((b : ℝ) + 2)
  let w := 56 * ((b : ℝ) + 3)^2 * ((b : ℝ) + 10)^4
  have h₁ := eventually_absorb_polylog (2 * p * d * w) 8 (show 1 - θ < 1 - θ/2 by linarith)
    (show (0 : ℝ) < 1/2 by norm_num)
  have h₂ := eventually_absorb_polylog (2 * A * p) 2 (show 3/4 - θ < 1 - θ/2 by linarith)
    (show (0 : ℝ) < 1/2 by norm_num)
  filter_upwards [h₁, h₂, eventually_ge_atTop 2] with n h₁ h₂ hn
  have hp := initialPositions_bound b n hn
  have hw := initialWidth_bound b n hn
  have hi := inv_two_pow_blockCount θ (show 1 ≤ n by omega)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let L := (n.log2 : ℝ) + 1
  let R := (processorCount b n : ℝ)
  calc
    _ ≤ ((p * R * (n : ℝ) ^ (3/4 : ℝ) * L^2) * d * (w * (n : ℝ) ^ (1/4 : ℝ) * L^6) +
          A * (p * R * (n : ℝ) ^ (3/4 : ℝ) * L^2)) * (2 * (n : ℝ) ^ (-θ)) := by
      rw [div_eq_mul_one_div]
      gcongr
    _ = R * ((2 * p * d * w) * (n : ℝ)^(1-θ) * L^8 + (2*A*p)*(n : ℝ)^(3/4-θ)*L^2) := by
      rw [show (1-θ) = (3/4+1/4)+(-θ) by ring, Real.rpow_add hnpos, Real.rpow_add hnpos,
        sub_eq_add_neg, Real.rpow_add hnpos]
      ring
    _ ≤ R * ((1/2)*(n : ℝ)^(1-θ/2) + (1/2)*(n : ℝ)^(1-θ/2)) := by gcongr
    _ = _ := by dsimp [R]; ring

/-- The fixed growth constant determines rational parameters as in Section 9.1. -/
structure PairExponents (C₂ : ℕ) where
  /-- Positive rational exponent governing the number of compression blocks, chosen to control
  growth under iteration. -/
  θ : ℚ
  /-- Positive rational slack exponent chosen smaller than one tenth of the compression
  exponent `θ`. -/
  δ : ℚ
  theta_pos : 0 < θ
  theta_lt : θ < 1/100
  delta_pos : 0 < δ
  delta_lt : δ < θ/10
  growth : (θ : ℝ) * Real.logb 2 C₂ ≤ 1/100

/-- Choose the two exponents for the compressed pair using only the fixed block's growth
constant. -/
noncomputable def pairExponents (B : S.Templates) : PairExponents B.growthConstant := by
  have hc : 1 ≤ (B.growthConstant : ℝ) := by
    exact_mod_cast (show 1 ≤ B.growthConstant by linarith [B.growthConstant_ge_two])
  apply Classical.choice
  obtain ⟨θ, δ, ht, ht', hd, hd', hg⟩ := exists_compression_exponents _ hc
  exact ⟨⟨θ, δ, ht, ht', hd, hd', hg⟩⟩

/-- Count local map, field and child occurrences over all final positions
using the actual placement fibers on a selected branch. -/
noncomputable def totalOccurrences {A : Type*} {N Y : NetworkKernel.Network}
    (chain : NetworkKernel.TermChain A N Y) : ℕ :=
  ∑ v : Y.Site, chain.occurrences (fun _ => 1) v

/-- Section 12 on the actual cursor graph and selected terms. The last
strict inequality bounds the sum over all final sites if each of their
recorded map occurrences contributes its allowed degree. -/
theorem eventually_pairBranchBounds (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      1 < virtualBits b n ∧ blockCount (u.θ : ℝ) n * S.laneBits ≤ virtualBits b n ∧
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f hf T hT X
        ∀ z : E.Choices,
          let Y := E.finalState z
          let chain := E.termChain (B.records f hf T hT X) z
          let fieldLimit := B.growthConstant ^ T * (X.maxWireWidth + 1)
          Y.positions ≤ initialPositions b n ∧
          (Y.totalWidth : ℝ) ≤ processorCount b n * (n : ℝ) ^ (1-u.θ/2 : ℝ) ∧
          (∀ v, (chain.occurrences (fun _ => 1) v : ℝ) ≤ (n : ℝ) ^ (1/100 : ℝ)) ∧
          chain.AllRecordsLe fieldLimit ∧ Y.maxWireWidth ≤ fieldLimit ∧
          (fieldLimit : ℝ) ≤ (n : ℝ) ^ (3/10 : ℝ) ∧
          (totalOccurrences chain : ℝ) ≤ initialPositions b n * (n : ℝ) ^ (1/100 : ℝ) ∧
          Y.positions * B.growthConstant ^ T * fieldLimit < 2 ^ (2 * addressBits b n) := by
  have hθ : 0 < (u.θ : ℝ) := by exact_mod_cast u.theta_pos
  have hθ' : (u.θ : ℝ) < 1/100 := by simpa using (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
  have hC : 1 ≤ (B.growthConstant : ℝ) := by
    exact_mod_cast (show 1 ≤ B.growthConstant by linarith [B.growthConstant_ge_two])
  have hr := cursorResource_bounds b S.laneBits hθ.le (by linarith) hC u.growth
    (A := 1) (by norm_num) hb
  have hw := eventually_widthEnvelope b S.baseDegree B.widthAllowance (Real.sqrt_nonneg _) hθ
  filter_upwards [hr, hw, eventually_ge_atTop 3] with n hr hw hn
  have hB : 5 ≤ b := (le_max_right _ _).trans hb
  have hclog := Nat.clog_pos (by decide : 1 < 2) (show 1 < n by omega)
  have hbits := addressBits_le_virtualBits b n hn
  have hD : 1 < virtualBits b n := by
    change b * Nat.clog 2 n ≤ virtualBits b n at hbits
    exact (show 1 < b * Nat.clog 2 n by nlinarith).trans_le hbits
  refine ⟨hD, by simpa only [Nat.mul_comm] using hr.1, ?_⟩
  intro base lanes labels hD hT A _ f hf X T E z Y chain L
  have h := B.branch_bounds f hf T hT X z
  change X.positions = S.positionFactor^T * Y.positions ∧ _ at h
  have hp := pairInput_positions S labels hD
  change X.positions = initialPositions b n at hp
  have hfactor : 0 < S.positionFactor ^ T := pow_pos (by linarith [S.positionFactor_gt_two]) _
  have hy : Y.positions ≤ initialPositions b n := hp ▸ h.1 ▸ Nat.le_mul_of_pos_left _ hfactor
  have hwin := pairInput_maxWireWidth S labels hD
  have hg := history_pow_blockCount_le hC hθ.le (show 1 ≤ n by omega) u.growth
  change (B.growthConstant : ℝ)^T ≤ (n : ℝ)^(1/100 : ℝ) at hg
  have hsize : (L : ℝ) ≤ (n : ℝ) ^ (3/10 : ℝ) := by
    change ((B.growthConstant^T * (X.maxWireWidth+1) : ℕ) : ℝ) ≤ _
    push_cast
    have hwin' : (X.maxWireWidth : ℝ) + 1 ≤ (initialWidth b n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hwin
    exact (mul_le_mul_of_nonneg_left hwin' (pow_nonneg (Nat.cast_nonneg _) _)).trans
      (by simpa only [one_mul] using hr.2.1)
  have hs : totalOccurrences chain ≤ Y.positions * B.growthConstant^T := by
    calc _ ≤ ∑ _v : Y.network.Site, B.growthConstant^T := Finset.sum_le_sum fun v _ => h.2.2.2.1 v
         _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
  have hcast : ((Y.positions * B.growthConstant^T : ℕ) : ℝ) ≤
      (initialPositions b n : ℝ) * (n : ℝ)^(1/100 : ℝ) := by
    push_cast
    gcongr
  have hs' : (totalOccurrences chain : ℝ) ≤ ((Y.positions * B.growthConstant^T : ℕ) : ℝ) := by
    exact_mod_cast hs
  refine ⟨hy, h.2.1.trans (h.2.2.1.trans (?_ : _ ≤ _)), fun v => ?_, h.2.2.2.2.1,
    h.2.2.2.2.2, hsize, hs'.trans hcast, ?_⟩
  · apply le_trans _ hw
    rw [hp]
    gcongr
    exact pairInput_sqrtEnergy S labels hD
  · have hv : (chain.occurrences (fun _ => 1) v : ℝ) ≤ (B.growthConstant : ℝ)^T := by
      exact_mod_cast h.2.2.2.1 v
    exact hv.trans hg
  · have hdeg := hsize.trans (Real.rpow_le_rpow_of_exponent_le
        (show 1 ≤ (n : ℝ) by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num : (3/10 : ℝ) ≤ 2/5))
    have hh := (mul_le_mul hcast hdeg (by positivity) (by positivity)).trans_lt hr.2.2
    rw [processorCount, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm (addressBits b n) 2] at hh
    exact_mod_cast hh

end CursorNetwork

end VPVNP
end Computability
end OAI
