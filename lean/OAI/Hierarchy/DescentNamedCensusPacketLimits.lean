import OAI.Hierarchy.DescentClosedReset
import OAI.Hierarchy.DescentPackedCensusInvoice
import OAI.Hierarchy.DescentWalshPrecisionNumbers
import OAI.Hierarchy.DescentRoundQuota
import OAI.Hierarchy.DescentFallbackShapeTable

namespace OAI
/-! # Incoming census coefficients and original donor digits fit the scheduled packet -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (p : ℕ)
local notation "cc" => S.groupWidth k tail i
local notation "b" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2

include B in
theorem named_census_packet_limits (gr : z=S.grainAt G.b p (i+1))
    (fee : wire=S.epochPower^S.priceExponent) (branch : G.b≤2^S.capGain) :
    k<2^b ∧ 1<2^b ∧ 2^k*(input.placement.wire*(input.placement.z*G.b)*input.placement.cap)<2^b ∧
    2*DescentFallbackShapeTable.rows k (2^n)≤2^(2*k+n+2) := by
  have enough := (input.placement.census_caps_at S input.valid ctl.height B.age.le
    (input.grain.trans gr) (input.edges.trans fee) branch).2
  have w : S.censusBits p ≤ S.localWalshBits p (cc+k) f (quota S.rounds) := by
    unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits
    omega
  refine ⟨(Nat.lt_two_pow_self (n:=k)).trans_le (Nat.pow_le_pow_right (by decide) (by omega)),
    ?_,?_,?_⟩
  · exact (show (1:ℕ)<2^1 by decide).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · have tight:=Nat.mul_lt_mul_of_pos_left enough (Nat.two_pow_pos k)
    rw [←pow_add] at tight
    exact tight.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · have y : 2^n+1 ≤ 2*2^n := by have := Nat.two_pow_pos n;omega
    calc
      2*DescentFallbackShapeTable.rows k (2^n)
          ≤2*((2^k*2^k)*(2*2^n)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n:=k))) y)
      _ = _ := by rw [show 2*k+n+2=k+k+n+2 by omega];simp only [pow_add];ring

/-- The actor scanner uses the preceding common-depth address in its four packet bounds. -/
theorem posted_actor_packet_limits (gr : z=S.grainAt G.b p (i+1))
    (fee : wire=S.epochPower^S.priceExponent) (branch : G.b≤2^S.capGain) :
    cc+k-B.terminals.commonDepth<2^b ∧ 1<2^b ∧
    2^(cc+k-B.terminals.commonDepth)*(input.placement.wire*(input.placement.z*G.b)*input.placement.cap)<2^b ∧
    2*DescentFallbackShapeTable.rows (cc+k-B.terminals.commonDepth) (2^B.reset.n)≤2^(2*k+n+2) :=by
  rw [B.commonDepth,B.dimension,Nat.add_sub_cancel_left]
  exact named_census_packet_limits B p gr fee branch

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
