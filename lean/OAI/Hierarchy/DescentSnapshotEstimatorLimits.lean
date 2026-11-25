import OAI.Hierarchy.DescentResetEstimatorWordRoom
import OAI.Hierarchy.DescentResetWalshScaleNumbers
import OAI.Hierarchy.DescentRoundQuota
import OAI.Hierarchy.DescentGlobalControlRoom
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Uniform word bounds for the exact reset Walsh score and stencil header -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh Filter
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F)
    (t f g reset τ B degreeMax : ℕ)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "tail_" h:arg => tail τ (J_ h)
local notation "S_" h:arg M:arg => stageNumbers G t (J_ h) f g reset M (tail_ h)
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)

/-- Nine times the external height suffices for all selected dates. The multiplier
is independent of the logarithmic divisor, the terminal tail and the graph. -/
theorem reset_estimator_words :
    ∀ᶠ h : ℕ in atTop, ∀ M p age D w : ℕ, M≤2^(2*h) → p≤h →
      age≤(S_ h M).length → D≤degreeMax → 9*h≤w →
      let m:=(S_ h M).groupWidth (k_ h) (tail_ h) age+k_ h
      let b:=(S_ h M).localWalshBits p m f (quota t)
      ResetEstimatorWords ((S_ h M).hostSize age) m b ((S_ h M).censusBits p) D w :=by
  let c:=hostRate t reset
  let a:=capRate G t g
  let coeff:=1+(c+a)*(t+1)+8+cutRate t f g
  let C:=(c+coeff)*(t+1)
  filter_upwards [eventually_actual_width G t f g reset B (quota t) τ,
    dyadic_log_room C 2,eventually_ge_atTop (max 3 degreeMax)] with h width poly high
  intro M p age D w sites inputSize ageAt degree bus
  dsimp only
  let J:=J_ h
  let S:=S_ h M
  let k:=k_ h
  let m:=S.groupWidth k (tail_ h) age+k
  let b:=S.localWalshBits p m f (quota t)
  change ResetEstimatorWords (S.hostSize age) m b (S.censusBits p) D w
  have logBound : J≤Nat.log 2 h:=Nat.div_le_self ..
  have tailFit : tail_ h≤τ*(Nat.log 2 h+1)^2:=by
    apply Nat.mul_le_mul_left
    exact (Nat.add_le_add_right logBound 1).trans (Nat.le_self_pow (by decide) _)
  have widthAt:=width M (tail_ h) age p inputSize tailFit ageAt
  have word : 8*b≤h/2:=widthAt.1
  have contents : 3*m+2*S.censusBits p+1≤b:=by
    change _≤3*m+2*S.censusBits p+DescentWalshPrecision.gainBits m f (quota t) (S.censusBits p)+1
    omega
  have deg : D≤h:=degree.trans ((le_max_right 3 degreeMax).trans high)
  have large : 3≤h:=(le_max_left 3 degreeMax).trans high
  have siteBits : (c+k)*age≤h:=by
    have kb : k≤coeff*(J+1):=groupBits_linear ..
    have ck : c+k≤(c+coeff)*(J+1):=by nlinarith only [kb,Nat.zero_le (c*J)]
    have dates : age≤(t+1)*(J+1):=ageAt.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
    calc
      (c+k)*age ≤ ((c+coeff)*(J+1))*((t+1)*(J+1)):=Nat.mul_le_mul ck dates
      _ = C*(J+1)^2:=by dsimp only [C];ring
      _ ≤ C*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right logBound 1) _)
      _ ≤ h:=poly
  have homes : S.hostSize age≤2^(3*h):=by
    change M*(2^c*2^k)^age≤_
    rw [←pow_add,←pow_mul]
    calc
      M*2^((c+k)*age) ≤ 2^(2*h)*2^h:=Nat.mul_le_mul sites (Nat.pow_le_pow_right (by decide) siteBits)
      _ = _:=by rw [←pow_add];congr 1; omega
  exact ResetEstimatorWords.of_sizes homes word contents deg large bus

end
end Hierarchy.DescentSixParty

end OAI
