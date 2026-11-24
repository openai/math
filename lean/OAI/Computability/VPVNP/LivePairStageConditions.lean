import OAI.Computability.VPVNP.LiveOutsideCallCapacity
import OAI.Computability.VPVNP.LiveProgramPairActive

/-! # Native first-half stage conditions at the paper's length parameters -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.LocalCount

open Filter CursorBounds BurstRAM PairStages PairStages.Group LiveAuxiliaryHeaders

/-- Conditions on the concrete RAM alone. The first inequality includes the
unpopulated header slots, so the address bound is uniform over every cut. -/
structure PairStageConditions (G : Group) (S H : ℕ) : Prop where
  room : ∀ i, Auxiliary.shadowBase G + span (Auxiliary.pairLengths G i) (Auxiliary.histLength G) ≤ 2^G.w
  width : 2*G.g.d < G.w
  nominations : 5*(2*G.g.d)+15 ≤ G.clockAt Stage.nominations
  initializer : 82 ≤ G.clockAt Stage.auxiliaryInit
  copy : 71 ≤ G.clockAt Stage.auxiliaryCopy
  exponents : 31 ≤ G.clockAt Stage.exponents
  labels : 0 < labelCount G
  row : 0 < expWidth G
  cost : OutsideBudget.actualBound G.constants G.g 0 false false true ≤ S
  bucket : 26 ≤ H

set_option exponentiation.threshold 10000 in
/-- The same address exponent as in the outside-work majorant suffices for
the native first-half calls and all their physical input arrays. -/
theorem eventually_pairStageConditions {C₂ : ℕ} (u : CursorNetwork.PairExponents C₂) (c : Constants) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ᶠ n : ℕ in atTop, ∀ G : Group,
      G.constants = c → G.g = paperGeometry B (liveCapacity u) n → n^10000 ≤ G.clock →
      PairStageConditions G (processorCount B n) (liveCapacity u n) := by
  obtain ⟨B₁,hmajor⟩ := OutsideBudget.eventually_budget c
  refine ⟨max 1 B₁,fun B hB => ?_⟩
  have h1 : 1 ≤ B := (le_max_left ..).trans hB
  have hspan : (Layout.shadow c + Auxiliary.headerSpan c).SitePowers :=
    ⟨Layout.shadow_sitePowers c, Auxiliary.headerSpan_sitePowers c⟩
  filter_upwards [(hspan.fits h1 (liveCapacity_polynomial u)).2,
    hmajor B ((le_max_right ..).trans hB), eventually_liveCapacity_ge u 26,
    eventually_ge_atTop 160, eventually_word_stage_le B B] with n hfit hsize hbucket hn hword
  intro G hc hg clock
  have hr (i : Fin (2^(Auxiliary.sizes G).h)) :
      Auxiliary.shadowBase G + span (Auxiliary.pairLengths G i) (Auxiliary.histLength G) ≤ 2^G.w := by
    rw [← Auxiliary.headerSpan_eval G i]
    change ((Layout.shadow G.constants + Auxiliary.headerSpan G.constants).eval G.g) ≤ 2^G.g.w
    rw [hc,hg]
    exact hfit.1.le
  have hd : G.g.d ≤ n := by
    rw [hg]
    exact (hword _ _ (Nat.mul_le_mul_left B (clog_le_log2_succ n)) (Nat.mul_le_mul_left B (clog_le_log2_succ n))).2
  have hwidth : 2*G.g.d < G.w := by
    change 2*G.g.d < G.g.w
    rw [hg]
    change 2*addressBits B n < (addressBits B n+10)^4
    have hs := Nat.pow_le_pow_right (Nat.succ_pos (addressBits B n+9)) (by decide : 2 ≤ 4)
    nlinarith only [hs]
  have h10 : 11*n ≤ n^10000 := calc
    _ ≤ n^2 := by rw [sq]; exact Nat.mul_le_mul_right n (by omega)
    _ ≤ n^10000 := Nat.pow_le_pow_right (by omega : 0<n) (by decide : 2 ≤ 10000)
  have clocks (s : Stage) : 11*n ≤ G.clockAt s + 44 := by
    have dispatch : (LiveStageLink.dispatchEvents G.addr s).length ≤ 44 := by
      simp only [LiveStageLink.dispatchEvents,List.length_cons,List.length_replicate]
      have := s.isLt
      omega
    exact (h10.trans clock).trans (by rw [← G.clock_add s]; omega)
  have hnG : 0 < G.g.n := by rw [hg]; exact (show 0<n by omega)
  have ht : 0 < labelCount G := by
    unfold labelCount Constants.labels
    rw [eval_add,Constants.grammarLabels_eq]
    unfold PrimedStackRAM.labelCount
    positivity
  have hz : 0 < expWidth G := by
    unfold expWidth Constants.Z Constants.height
    rw [eval_mul,PublicExpr.eval_natPow]
    exact Nat.mul_pos (show 0 < 2 by decide) (Nat.pow_pos hnG)
  have hout := OutsideBudget.actual_le G.constants G.g 0 false false true (by rw [hg]; exact hsize.2) (Nat.zero_le _)
  have hbudget : OutsideBudget.actualBound G.constants G.g 0 false false true ≤ processorCount B n := by
    apply hout.trans
    rw [hc,hg]
    exact hsize.1.le
  exact ⟨hr,hwidth,by have := clocks Stage.nominations; omega,by have := clocks Stage.auxiliaryInit; omega,
    by have := clocks Stage.auxiliaryCopy; omega,by have := clocks Stage.exponents; omega,ht,hz,hbudget,hbucket⟩

end LiveProgram.LocalCount

end VPVNP
end Computability
end OAI
