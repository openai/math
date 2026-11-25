import OAI.Computability.NearSquareRoot.PhysicalWalshRouterClock
import OAI.Computability.NearSquareRoot.PhysicalWalshXorThreshold
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapPrefix
import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryRouter

/-! # The clock of the width-dependent front XOR

The elementary pass is selected below the threshold needed for the interior
XOR. Above that threshold the native gate scans the dyadically extended prefix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontClock

open PhysicalWalsh ElementarySchedule

/-- Bit payload of the padded array, including both signed components. -/
def volume (A W : ℕ) (s : Shape) := SwapPrefix.paddedSize A W s * (2*(s.w+1))

/-- Extra clock for the actual side of the native-gate threshold. -/
noncomputable def extra (A W : ℕ) (ρ : ℝ) (D : ℕ) (s : Shape) : ℕ :=
  if slotWidth A s < XorThreshold.cutoff D (Header.scale A s) then ElementarySweep.extra A s
  else XorThreshold.gateClock ρ (slotWidth A s) (volume A W s)

private theorem volume_le (A W : ℕ) (s : Shape) :
    volume A W s ≤ 4*((count A s+1)*(s.w+1)) := by
  have bound := (SwapPrefix.paddedSize_le A W s).trans
    (Nat.mul_le_mul_left 2 (SwapPrefix.length_le_count A W s))
  calc
    _ ≤ (2*count A s)*(2*(s.w+1)) := Nat.mul_le_mul_right _ bound
    _ ≤ 4*((count A s+1)*(s.w+1)) := by ring_nf; omega

theorem clog_le (Q : ℕ) : (Nat.clog 2 (Q+1):ℝ) ≤ 3*(1+Real.log (2+Q)) := by
  have coef : 1+(Real.log 2)⁻¹ ≤ 3 := by
    have h := (inv_le_comm₀ (Real.log_pos (by norm_num : (1:ℝ)<2)) (by norm_num : (0:ℝ)<2)).mpr
      (show (2:ℝ)⁻¹ ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    linarith
  exact (RouterClock.clog_logWidth Q).trans
    (mul_le_mul_of_nonneg_right coef (zero_le_one.trans (RouterClock.one_le_logWidth _)))

theorem small_bound {A D : ℕ} {ρ : ℝ} {s : Shape}
    (small : slotWidth A s ≤ XorThreshold.cutoff D (Header.scale A s)) :
    (ElementarySweep.extra A s : ℝ) ≤ (7+3*(D:ℝ))*RouterClock.unit A ρ s := by
  let Q := Header.scale A s
  let B : ℝ := ((count A s+1)*(s.w+1) : ℕ)
  let Z := 1+Real.log (2+(Q:ℝ))
  let F := 1+(slotWidth A s:ℝ)^ρ
  have hz : 1 ≤ Z := RouterClock.one_le_logWidth _
  have hf : 1 ≤ F := by dsimp [F]; linarith [Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) (slotWidth A s)) ρ]
  have hb : 0 ≤ B := Nat.cast_nonneg _
  have width : slotWidth A s+1 ≤ 7+D*Nat.clog 2 (Q+1) := by
    change slotWidth A s ≤ max 6 (D*Nat.clog 2 (Q+1)) at small; omega
  have realWidth : (slotWidth A s+1 : ℕ) ≤ 7+(D:ℝ)*Nat.clog 2 (Q+1) := by exact_mod_cast width
  have c := mul_le_mul_of_nonneg_left (clog_le Q) (Nat.cast_nonneg (α:=ℝ) D)
  have bound : ((slotWidth A s+1:ℕ):ℝ) ≤ (7+3*(D:ℝ))*Z := by
    change (D:ℝ)*Nat.clog 2 (Q+1) ≤ D*(3*Z) at c
    linarith only [realWidth,c,hz]
  change (((slotWidth A s+1)*((count A s+1)*(s.w+1)) : ℕ):ℝ) ≤ _
  rw [Nat.cast_mul]
  change _ ≤ (7+3*(D:ℝ))*(B*Z*F)
  calc
    _ ≤ ((7+3*(D:ℝ))*Z)*B := mul_le_mul_of_nonneg_right bound hb
    _ ≤ ((7+3*(D:ℝ))*Z)*B*F := le_mul_of_one_le_right (by positivity) hf
    _ = _ := by ring

theorem large_bound {a : ℕ} (W : ℕ) {ρ : ℝ} (lower : 0 ≤ ρ) (upper : ρ ≤ 1) (s : Shape) :
    (XorThreshold.gateClock ρ (slotWidth (a+1) s) (volume (a+1) W s):ℝ) ≤
      5505*RouterClock.unit (a+1) ρ s := by
  let A := a+1
  let L := slotWidth A s
  let Q := Header.scale A s
  let B : ℝ := ((count A s+1)*(s.w+1) : ℕ)
  let Z := 1+Real.log (2+(Q:ℝ))
  let F := 1+(L:ℝ)^ρ
  have hz : 1 ≤ Z := RouterClock.one_le_logWidth _
  have hf : 1 ≤ F := by dsimp [F]; linarith [Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) L) ρ]
  have hb : 1 ≤ B := by dsimp only [B]; exact_mod_cast Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have cover : 1 ≤ B*Z*F := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hb hz) hf
  have fit : L ≤ Q := ElementarySweep.slotWidth_le_scale a s
  have big : 2 ≤ Q := by dsimp [Q]; rw [Header.scale_exact]; omega
  have pos : 0 < L := by dsimp [L,slotWidth,grow,A]; positivity
  have run := XorThreshold.clock_rate lower upper pos fit big (volume A W s)
  have vol : (volume A W s:ℝ) ≤ 4*B := by dsimp only [B]; exact_mod_cast volume_le A W s
  have scaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left vol
    (show 0 ≤ 1376*Z by positivity)) (show 0 ≤ F by positivity)
  change (XorThreshold.gateClock ρ L (volume A W s):ℝ) ≤ 1376*Z*(volume A W s)*F+1 at run
  change (XorThreshold.gateClock ρ L (volume A W s):ℝ) ≤ 5505*(B*Z*F)
  linarith only [run,scaled,cover]

/-- A common multiplier for both sides of the threshold, independent of
the node's level, word width and spectator lengths. -/
theorem extra_bound {a : ℕ} (W D : ℕ) {ρ : ℝ} (lower : 0 ≤ ρ) (upper : ρ ≤ 1) (s : Shape) :
    (extra (a+1) W ρ D s:ℝ) ≤ (5505+3*(D:ℝ))*RouterClock.unit (a+1) ρ s := by
  have nonneg := zero_le_one.trans (RouterClock.one_le_unit (a+1) ρ s)
  unfold extra
  split_ifs with small
  · exact (small_bound small.le).trans (mul_le_mul_of_nonneg_right (by linarith) nonneg)
  · exact (large_bound W lower upper s).trans (mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α:=ℝ) D]) nonneg)

/-- Total extra scans at a node after the two machine degrees are fixed, covering
the low-position passes, whole-field swaps, and central XOR. -/
theorem combined_clock {a : ℕ} (W swapDegree frontDegree : ℕ) (arity : 2 ≤ a+1)
    {ρ : ℝ} (lower : 0 ≤ ρ) (upper : ρ ≤ 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s, withinWidth (a+1) s →
      ((ElementarySweep.prefixExtra (a+1) (SlotSwap.reserve swapDegree (a+1)) s +
        SlotSwap.wideExtra ρ (a+1) s + extra (a+1) W ρ frontDegree s : ℕ):ℝ) ≤
        localTime (a+1) ρ c (RouterClock.logWidth s.w) 0 s.level (bitVolume (a+1) s) :=
  RouterClock.combined_clock swapDegree arity lower (by positivity : 0 ≤ 5505+3*(frontDegree:ℝ))
    (fun s _ => extra_bound W frontDegree lower upper s)

end PhysicalWalshNode.FrontClock

end NearSquareRoot
end Computability
end OAI
