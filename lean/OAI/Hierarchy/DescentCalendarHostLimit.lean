import OAI.Hierarchy.DescentDatedSmallAddress
import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! # Address sizes of the true chronological group and host arrays -/
namespace Hierarchy.DescentDatedAddressBook
open DescentCompiler DescentSixParty DescentCompiler.TerminalScale Filter
variable {F : Type} [Field F] (G : PoweredGadget F)
variable {ι : ℕ→Type*} (t f g reset τ B : ℕ) (sites age : ∀h,ι h→ℕ)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (τ*(J_ h+1))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g

/-- Input sites occupy at most two external words of exponent. All host growth
over the whole calendar occupies at most one more, for every fixed τ and B. -/
theorem scheduled_host_limit (source : ∀h i,sites h i≤(2^h)^2)
    (before : ∀h i,age h i≤(S_ h i).length+1) :
    ∀ᶠ h:ℕ in atTop,∀i,(S_ h i).hostSize (age h i)≤2^(3*h) :=by
  let c:=hostRate t reset
  let C:=(c+κ)*(t+2)
  have powers (h b : ℕ) (hb:b≤(t+1)*(J_ h)+1) : (c+k_ h)*b≤C*(J_ h+1)^2:=by
    have kw:=groupBits_linear t (J_ h) c (capRate G t g) (cutRate t f g)
    have lo : c+k_ h≤(c+κ)*(J_ h+1):=by
      change (k_ h)≤κ*(J_ h+1) at kw
      nlinarith only [kw,Nat.zero_le (c*(J_ h))]
    have hi : b≤(t+2)*(J_ h+1):=by nlinarith only [hb,Nat.zero_le t,Nat.zero_le (J_ h)]
    exact (Nat.mul_le_mul lo hi).trans_eq (by dsimp only [C];ring)
  filter_upwards [dyadic_log_room C 2] with h paid
  intro i
  have exp := (powers h (age h i) (before h i)).trans ((Nat.mul_le_mul_left C
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.div_le_self ..) 1) 2)).trans paid)
  change sites h i*(2^c*2^(k_ h))^(age h i)≤2^(3*h)
  rw [←pow_add,←pow_mul]
  have m:=Nat.mul_le_mul (source h i) (Nat.pow_le_pow_right (by decide : 0<2) exp)
  calc
    _ ≤ (2^h)^2*2^h:=m
    _ = _ :=by rw [←pow_mul,←pow_add];congr 1;ring


end Hierarchy.DescentDatedAddressBook

end OAI
