import OAI.Hierarchy.DescentWalshWordBounds
import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentPrivateClockScale

namespace OAI
/-! # Uniform local word width for the logarithmic epoch and every occupied age -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentWalshPrecision DescentPackedWalsh
variable {F : Type} [Field F] (G : PoweredGadget F)

def massCoefficient (S : AtomSchedule) :=
  1+S.censusExponent
def dimCoefficient (S : AtomSchedule) (cut tailFactor : ℕ) :=
  tailFactor+privateGroupRate S.rounds S.hostGain S.capGain cut
def localCoefficient (t f g reset K tailFactor : ℕ) :=
  let S:=stageNumbers G t 0 f g reset 0 0
  4*dimCoefficient S (cutRate t f g) tailFactor+3*massCoefficient S+f+2*Nat.clog 2 K+11

theorem actual_width (t J f g reset M tail i h p K T : ℕ)
    (payload : p≤h) (logAge : J≤Nat.log 2 h) (tailRoom : tail≤T*(Nat.log 2 h+1)^2)
    (_valid : i≤(t+1)*J) :
    let S:=stageNumbers G t J f g reset M tail
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    let m:=S.groupWidth k tail i+k
    S.localWalshBits p m f K≤localCoefficient G t f g reset K T*(Nat.log 2 h+1)^2 := by
  let S:=stageNumbers G t J f g reset M tail
  let L:=Nat.log 2 h+1
  let cut:=cutRate t f g
  let k:=groupBits t J S.hostGain S.capGain cut
  let m:=S.groupWidth k tail i+k
  have posL : 0<L := Nat.succ_pos _
  have sub : J+1≤L := Nat.succ_le_succ logAge
  have hL : L≤L^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ posL
  have one : 1≤L^2 := (Nat.succ_le_of_lt posL).trans hL
  have len : S.length+1≤(t+1)*L := by
    change (t+1)*J+1≤_
    have cost:=Nat.mul_le_mul_left (t+1) sub
    rw [Nat.mul_succ] at cost
    omega
  have kj : k≤(1+(S.hostGain+S.capGain)*(t+1)+8+cut)*L :=
    (groupBits_linear t J S.hostGain S.capGain cut).trans (Nat.mul_le_mul_left _ sub)
  have smallM : m≤dimCoefficient S cut T*L^2 := by
    have short : k*((S.length-i)+1)≤k*(S.length+1) := Nat.mul_le_mul_left _ (by omega)
    have prod:=Nat.mul_le_mul kj len
    change tail+k*(S.length-i)+k≤_
    change tail≤T*L^2 at tailRoom
    change _≤(T+(1+(S.hostGain+S.capGain)*(t+1)+8+cut)*(t+1))*L^2
    nlinarith only [short,prod,tailRoom]
  have smallMass : S.censusBits p ≤ massCoefficient S*L := by
    have grow := Nat.lt_pow_succ_log_self (by decide : 1<2) h
    have header : Nat.clog 2 (p+1)≤L := Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (payload.trans_lt grow))
    have grain:=Nat.mul_le_mul_right S.censusExponent (show J≤L by omega)
    change Nat.clog 2 (p+1)+J*S.censusExponent≤(1+S.censusExponent)*L
    nlinarith only [header,grain]
  have mag:=smallMass.trans (Nat.mul_le_mul_left (massCoefficient S) hL)
  have overhead : f+2*Nat.clog 2 K+11≤(f+2*Nat.clog 2 K+11)*L^2 :=
    Nat.le_mul_of_pos_right _ one
  have div_ := Nat.div_le_self (m+7) 8
  have eff : rate m K ≤ m+2*Nat.clog 2 K+9 := by unfold rate;omega
  change 3*m+2*S.censusBits p+(f+S.censusBits p+rate m K+1)+1≤
    (4*dimCoefficient S cut T+3*massCoefficient S+f+2*Nat.clog 2 K+11)*L^2
  nlinarith only [smallM,mag,eff,overhead]

/-- Sufficiently large external heights price every age, all optional extra
group digits and the original level and gain words simultaneously. -/
theorem eventually_actual_width (t f g reset B K T : ℕ) :
    ∀ᶠ h : ℕ in Filter.atTop,∀M tail i p,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M tail
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let m:=S.groupWidth k tail i+k
      let b:=S.localWalshBits p m f K
      let g₀:=gainBits m f K (S.censusBits p)
      p≤h→tail≤T*(Nat.log 2 h+1)^2→i≤S.length→
        8*b≤h/2 ∧ g₀+b*2^laneBits m h b≤h/2 ∧ m+Nat.clog 2 (m+2)+8*b≤h/2 := by
  filter_upwards [eventually_log_square (32*localCoefficient G t f g reset K T)] with h hh
  intro M tail i p
  dsimp only
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M tail
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let m:=S.groupWidth k tail i+k
  let b:=S.localWalshBits p m f K
  let gy:=gainBits m f K (S.censusBits p)
  change _→_→_→8*b≤h/2 ∧ gy+b*2^laneBits m h b≤h/2 ∧ m+Nat.clog 2 (m+2)+8*b≤h/2
  intro payload tailRoom age
  have bounded : b≤localCoefficient G t f g reset K T*(Nat.log 2 h+1)^2 :=
    actual_width G t J f g reset M tail i h p K T payload (Nat.div_le_self ..) tailRoom age
  have width : 32*b≤h := (Nat.mul_le_mul_left 32 bounded).trans (by simpa only [Nat.mul_assoc] using hh)
  have bp : 0<b := Nat.succ_pos _
  have split : 8*b≤h/2 := by omega
  have ml : 3*m+1≤b := by
    change _≤3*m+2*S.censusBits p+gy+1
    omega
  have mg : Nat.clog 2 (m+2) ≤ m+2 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  exact ⟨split,packed_key bp split (gain_le ..),by omega⟩

end Hierarchy.DescentSixParty

end OAI
