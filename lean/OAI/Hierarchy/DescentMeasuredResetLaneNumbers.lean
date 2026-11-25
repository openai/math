import OAI.Hierarchy.DescentResetWalshScaleNumbers
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! # The measured Walsh word contains a whole selected reset subcube -/
namespace Hierarchy.DescentSixParty
open Filter DescentCompiler DescentPackedWalsh
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The native low-word width can be split into the genuine reset block and a dyadic
number of neighboring blocks. The estimate is uniform in the preceding branch and age. -/
theorem measured_lane_room (t f g reset τ B K : ℕ)
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B) :
    ∀ᶠ h : ℕ in atTop, ∀M i p,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (τ*(J+1))
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let m:=S.groupWidth k (τ*(J+1)) i+k
      let b:=S.localWalshBits p m f K
      i≤S.length → p≤h → k≤laneBits m h b := by
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let C:=localCoefficient G t f g reset K τ
  filter_upwards [dyadic_log_room ((8*C)^2) 4,eventually_ge_atTop (2^(2*B))] with h cost late
  intro M i p
  dsimp only
  let L:=Nat.log 2 h
  let J:=L/(2*B)
  let S:=stageNumbers G t J f g reset M (τ*(J+1))
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let m:=S.groupWidth k (τ*(J+1)) i+k
  let b:=S.localWalshBits p m f K
  intro age paid
  have cut : 2*κ≤B:=cutoff
  have pos : 0<2*B:=by dsimp [κ] at cut; omega
  have floor : 2*B≤L:=Nat.le_log_of_pow_le (by decide) late
  have start : 0<J:=(Nat.le_div_iff_mul_le pos).2 (by simpa using floor)
  have jL : J≤L:=Nat.div_le_self ..
  have span : τ*(J+1)≤τ*(L+1)^2:=by
    exact Nat.mul_le_mul_left _ ((Nat.succ_le_succ jL).trans (by nlinarith))
  have bk : k≤κ*(J+1):=groupBits_linear ..
  have rb : b≤C*(L+1)^2:=actual_width G t J f g reset M (τ*(J+1)) i h p K τ paid jL span age
  have small : (8*b)^2≤h:=by
    calc
      (8*b)^2 ≤ (8*(C*(L+1)^2))^2:=Nat.pow_le_pow_left (Nat.mul_le_mul_left _ rb) _
      _ = (8*C)^2*(L+1)^4:=by ring
      _ ≤ h:=cost
  have double : 2*k≤L:=by
    have a:=Nat.mul_le_mul_left κ (show J+1≤2*J by omega)
    have b₁:=Nat.mul_le_mul_right J cut
    have c:=Nat.div_mul_le_self L (2*B)
    change J*(2*B)≤L at c
    nlinarith only [bk,a,b₁,c]
  have hk : (2^k)^2≤h:=by
    rw [←pow_mul]
    apply (Nat.le_log_iff_pow_le (by decide) (show h≠0 by have :=Nat.two_pow_pos (2*B);omega)).mp
    omega
  have fits : 2^k*(8*b)≤h:=by
    rcases le_total (2^k) (8*b) with le|le
    · exact (Nat.mul_le_mul_right _ le).trans (by simpa only [pow_two] using small)
    · exact (Nat.mul_le_mul_left _ le).trans (by simpa only [pow_two] using hk)
  have bp : 0<8*b:=by
    dsimp [b,AtomSchedule.localWalshBits,DescentWalshPrecision.bits]
    omega
  exact le_min (by change k≤S.groupWidth k (τ*(J+1)) i+k;omega)
    (Nat.le_log_of_pow_le (by decide) ((Nat.le_div_iff_mul_le bp).2 fits))

end Hierarchy.DescentSixParty

end OAI
