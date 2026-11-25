import OAI.Hierarchy.DescentNamedCensusPacketLimits
import OAI.Hierarchy.DescentCapCalendarPositive

namespace OAI
/-! # Physical census and arrival sizes at a measured reset -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (p : ℕ)
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

include B in
theorem posted_census_limits (positive:0< p) (gr:z=S.grainAt G.b p (i+1))
    (fee:wire=S.epochPower^S.priceExponent) (branch:G.b≤2^S.capGain)
    (capAt:input.placement.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256) :
    0< amp ∧ amp<2^(S.censusBits p) ∧ 2*input.placement.cap<2^(S.censusBits p) := by
  have mass := (input.placement.census_caps_at S input.valid ctl.height B.age.le
    (input.grain.trans gr) (input.edges.trans fee) branch).2
  have grain : 0< input.placement.z := (input.grain.trans gr).symm ▸ S.grain_positive G.base_pos positive (i+1)
  have cap : 0< input.placement.cap := by
    rw [capAt]
    exact Nat.mul_pos (Chronology.DonorDate.prefix_cap_pos G.b S.rounds g S.height i G.base_pos) (by decide)
  have amount : 2≤ input.placement.wire := by
    rw [input.edges,fee]
    have atLeast : 2≤ S.epochPower := by
      change 2≤2^S.height
      exact (show 2=2^1 by decide).le.trans (Nat.pow_le_pow_right (by decide) ctl.height)
    have exponent : 0< S.priceExponent := by unfold AtomSchedule.priceExponent atomExponent;omega
    exact atLeast.trans (Nat.le_self_pow (by omega) _)
  have two : 2≤ input.placement.wire*(input.placement.z*G.b) :=
    amount.trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos grain G.base_pos))
  exact ⟨Nat.mul_pos (by omega) cap,mass,(Nat.mul_le_mul_right _ two).trans_lt mass⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
