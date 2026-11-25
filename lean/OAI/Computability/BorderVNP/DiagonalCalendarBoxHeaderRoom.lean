import OAI.Computability.BorderVNP.DiagonalChosenSignedCalendar
import OAI.Computability.BorderVNP.DiagonalLocatedSignedGrid
import OAI.Computability.BorderVNP.GeometryAdviceCharge

/-! # The original signed box length fits its own header -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Cover Epoch Packing Packing.DeckGrid Crossing Branch PackedHistoryCircuit TeamScales GeometryAdviceRate
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube

private theorem description_fits_seed_header {D n r d copies header : ℕ}
    (hn : 1≤n) (hr : 1≤r) (replicated : 0<copies) (wide : 0<header)
    (budget : 1+initialMass (D:=D) n r d copies header ≤ TeamScales.width n (1/2)) :
    let axes := Fintype.card (Cube D)
    let cap := seedBoxCapacity n r axes d (Fintype.card (Direction axes))
    seedDescriptionWidth n r axes d (header*logWidth r n) (BottomGridBank.bodyBudget cap) < 2^(header*logWidth r n) := by
  intro axes cap
  let desc := seedDescriptionWidth n r axes d (header*logWidth r n) (BottomGridBank.bodyBudget cap)
  let term := 2*cap+desc+(2*Fintype.card (Direction axes)+1)*seedChannelWidth n r axes d
  have upper := Nat.le_mul_of_pos_left term replicated
  have packet : desc ≤ initialMass (D:=D) n r d copies header := by
    change desc ≤ seedPublicBase (Fintype.card (Direction axes))+12+810487*cap+copies*term
    have inside : desc≤term := by dsimp only [term]; omega
    omega
  have capped : TeamScales.width n (1/2) ≤ n := by
    unfold TeamScales.width
    apply Nat.floor_le_of_le
    have root := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤n by exact_mod_cast hn)
      (show (1/2:ℝ)≤1 by norm_num)
    simpa only [Real.rpow_one] using root
  have log := (GeometryAdviceRate.indexWidths hr hn).2.1
  have maximum := (Nat.le_pow_clog (by decide : 1<2) (n+1)).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (log.trans (Nat.le_mul_of_pos_left _ wide)))
  change desc<_
  omega

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))

include cal in
/-- The original seed reserves each entire description below the true
factor-header capacity, uniformly before selecting a history or a bundle. -/
theorem SignedCalendarAt.frozenDescription_headerRoom
    (grid : LocatedSignedGridAt cube b header (l+1)) [Fact (8≤header)] :
    let r := stretch b.ρ (l+1)
    let d := CoverScale.initialDepth (Cube D) r (l+1)-1
    let axes := Fintype.card (Cube D)
    let cap := seedBoxCapacity (l+1) r axes d (Fintype.card (Direction axes))
    seedDescriptionWidth (l+1) r axes d (header*logWidth r (l+1)) (BottomGridBank.bodyBudget cap) <
      2^(header*logWidth r (l+1)) := by
  have copies : 0<TeamScales.width (l+1) scales.α := by
    by_contra! empty
    have zero := Nat.eq_zero_of_le_zero empty
    have count := grid.count
    simp only [zero,Nat.mul_zero] at count
    omega
  exact description_fits_seed_header (D:=D) (Nat.succ_pos l) (stretch_one b.ρ (l+1)) copies
    (by have wide : 8≤header := Fact.out; omega) cal.seed.choose_spec.choose_spec.2.2.2.2

end Diagonal

end BorderVNP
end Computability
end OAI
