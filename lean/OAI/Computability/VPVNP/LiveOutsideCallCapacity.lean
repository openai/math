import OAI.Computability.VPVNP.LiveOutsideTailStages
import OAI.Computability.VPVNP.PaperPairParameters

/-!
# Eventual call and instruction caps for the live group's outside work

The only growing probe count is the gather of a physical word on a tail
route. Its quartic logarithmic width fits inside the live bucket. The
nomination sweep and the tail gather have linearly many private instructions
in the address width and word width respectively. All estimates hold before
choosing a group, an input header or a successful branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideBudget

open BurstRAM CursorBounds Compression CursorNetwork Filter

/-- Every outside report, including a gather of all bits of one physical
word, fits the per-call capacity of the live machine. -/
theorem eventually_outsideCalls_le (B : ℕ) {δ : ℝ} (hδ : δ < 1) :
    ∀ᶠ n : ℕ in atTop, max 26 (OutsideTailStages.callBound (CursorBounds.wordBits B n)) ≤ liveBucket δ n := by
  let A := (B+10)^4+26
  filter_upwards [eventually_polylog_le_rpow A 4 (sub_pos.mpr hδ), eventually_ge_atTop 1] with n hpoly hn
  let L := n.log2+1
  have hd : addressBits B n ≤ B*L := Nat.mul_le_mul_left B (clog_le_log2_succ n)
  have hwidth : addressBits B n+10 ≤ (B+10)*L := by
    rw [Nat.add_mul]
    have : 1 ≤ L := Nat.succ_pos _
    omega
  have hw : CursorBounds.wordBits B n ≤ (B+10)^4*L^4 := by
    simpa only [CursorBounds.wordBits, mul_pow] using Nat.pow_le_pow_left hwidth 4
  have hone : 1 ≤ L^4 := Nat.pow_pos (Nat.succ_pos _) (n := 4)
  have hsum : max 26 (OutsideTailStages.callBound (CursorBounds.wordBits B n)) ≤ A*L^4 := by
    unfold A OutsideTailStages.callBound
    rw [Nat.add_mul]
    omega
  have hcap := hpoly.trans (liveBucket_bounds hδ.le hn).1
  exact hsum.trans (by exact_mod_cast hcap)

set_option exponentiation.threshold 10000 in
/-- The actual private work of each outside stage fits the fixed live
private-instruction clock of Section 14.2. -/
theorem eventually_outsideInstructions_le (B : ℕ) (E : UniversalMachine.Program) :
    ∀ᶠ n : ℕ in atTop, max 154 (max (5*(2*addressBits B n)+23)
      (max 130 (max (8*CursorBounds.wordBits B n+67) (LiveEvaluatorRAM.Schedule.callFuel E+47)))) ≤ n^10000 := by
  filter_upwards [eventually_word_stage_le B B, eventually_ge_atTop (max 154 (LiveEvaluatorRAM.Schedule.callFuel E+47))]
    with n hword hlarge
  have hd : addressBits B n ≤ B*(n.log2+1) := Nat.mul_le_mul_left B (clog_le_log2_succ n)
  obtain ⟨hw, hdn⟩ := hword (addressBits B n) (addressBits B n) hd hd
  change CursorBounds.wordBits B n ≤ n at hw
  have hn : 154 ≤ n := (le_max_left ..).trans hlarge
  have hwork : max 154 (max (5*(2*addressBits B n)+23)
      (max 130 (max (8*CursorBounds.wordBits B n+67) (LiveEvaluatorRAM.Schedule.callFuel E+47)))) ≤ 11*n := by omega
  have hsq : 11*n ≤ n^2 := by rw [sq]; exact Nat.mul_le_mul_right n (by omega)
  exact hwork.trans (hsq.trans (Nat.pow_le_pow_right (lt_of_lt_of_le (by decide : 0 < 154) hn) (by decide : 2 ≤ 10000)))

/-- The paper's exact rounded live bucket and the concrete instruction
clocks of all three group modes, uniformly in the choice of group. -/
theorem eventually_groupReportCaps {C : ℕ} (u : PairExponents C) (B : ℕ) (E : UniversalMachine.Program) :
    ∀ᶠ n : ℕ in atTop, ∀ G : PairStages.Group, G.g = paperGeometry B (liveCapacity u) n → G.evaluator = E →
      max 26 (OutsideTailStages.callBound G.w) ≤ G.g.H ∧
      max 154 (max (5*(2*G.g.d)+23) (OutsideTailStages.instructionBound G)) ≤ n^10000 := by
  have hδ : (u.δ : ℝ) < 1 := by exact_mod_cast (show u.δ < 1 by linarith [u.delta_lt,u.theta_lt])
  filter_upwards [eventually_outsideCalls_le B hδ, eventually_outsideInstructions_le B E] with n hc hw
  intro G hg he
  rw [← liveCapacity_eq u n] at hc
  unfold OutsideTailStages.instructionBound PairStages.Group.w
  rw [hg, he]
  exact ⟨hc, hw⟩

end LiveProgram.OutsideBudget

end VPVNP
end Computability
end OAI
