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

structure ScheduleSpace : Prop where
  oldHost : Bounded (fun h i=>(S_ h i).hostSize (age h i))
  newHost : Bounded (fun h i=>(S_ h i).hostSize (age h i+1))
  oldGroup : Bounded (fun h i=>(S_ h i).groupCount (age h i))
  newGroup : Bounded (fun h i=>(S_ h i).groupCount (age h i+1))
  matrices : Bounded (fun h i=>let dim:=(S_ h i).groupWidth (k_ h) (τ*(J_ h+1)) (age h i)+k_ h;2^(dim*dim))
  halfMatrix : ∀ᶠ h:ℕ in atTop,∀i,let dim:=(S_ h i).groupWidth (k_ h) (τ*(J_ h+1)) (age h i)+k_ h;dim*dim≤h/2

theorem schedule_space (source : Bounded sites) (before : ∀h i,age h i≤(S_ h i).length) :
    ScheduleSpace G t f g reset τ B sites age :=by
  let c:=hostRate t reset
  let A:=τ+κ*(t+2)
  let C:=(c+κ)*(t+2)
  have dims (h b : ℕ) :
      τ*(J_ h+1)+(k_ h)*((t+1)*(J_ h)-b)+(k_ h)≤A*(J_ h+1)^2 :=by
    have k₀:=groupBits_linear t (J_ h) c (capRate G t g) (cutRate t f g)
    let j:=J_ h
    change (k_ h)≤κ*(j+1) at k₀
    have orbit:=Nat.mul_le_mul k₀ (Nat.sub_le ((t+1)*j) b)
    change τ*(j+1)+(k_ h)*((t+1)*j-b)+(k_ h)≤(τ+κ*(t+2))*(j+1)^2
    nlinarith only [orbit,k₀,Nat.zero_le (τ*j),Nat.zero_le (τ*j*j),
      Nat.zero_le (κ*j),Nat.zero_le (κ*j*j),Nat.zero_le (κ*t*j),Nat.zero_le (κ*t)]
  have powers (h b : ℕ) (hb:b≤(t+1)*(J_ h)+1) : (c+k_ h)*b≤C*(J_ h+1)^2:=by
    have kw:=groupBits_linear t (J_ h) c (capRate G t g) (cutRate t f g)
    have lo : c+k_ h≤(c+κ)*(J_ h+1):=by
      change (k_ h)≤κ*(J_ h+1) at kw
      nlinarith only [kw,Nat.zero_le (c*(J_ h))]
    have hi : b≤(t+2)*(J_ h+1):=by nlinarith only [hb,Nat.zero_le t,Nat.zero_le (J_ h)]
    exact (Nat.mul_le_mul lo hi).trans_eq (by dsimp only [C];ring)
  have exponent (j : ∀h,ι h→ℕ) (room : ∀h i,j h i≤(t+1)*(J_ h)+1) :
      Bounded (fun h i=>2^((c+k_ h)*j h i)) :=by
    apply Bounded.pow_of_linear (K:=1)
    filter_upwards [dyadic_log_room C 2] with h bound
    intro i
    rw [Nat.one_mul]
    exact (powers h (j h i) (room h i)).trans ((Nat.mul_le_mul_left C
      (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.div_le_self ..) 1) 2)).trans bound)
  have hosts (j : ∀h,ι h→ℕ) (room : ∀h i,j h i≤(t+1)*(J_ h)+1) :
      Bounded (fun h i=>(S_ h i).hostSize (j h i)) :=by
    convert source.mul (exponent j room) using 1
    funext h i
    change sites h i*(2^c*2^(k_ h))^(j h i)=_
    rw [←pow_add,←pow_mul]
  have groups (j : ∀h,ι h→ℕ) : Bounded (fun h i=>(S_ h i).groupCount (j h i)):=by
    have fitt : Bounded (fun h i=>2^((S_ h i).groupWidth (k_ h) (τ*(J_ h+1)) (j h i))) :=by
      apply Bounded.pow_of_linear (K:=1)
      filter_upwards [dyadic_log_room A 2] with h bound
      intro i
      have small:=dims h (j h i)
      have ge:=Nat.mul_le_mul_left A (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.div_le_self (Nat.log 2 h) (2*B)) 1) 2)
      change τ*(J_ h+1)+(k_ h)*((t+1)*(J_ h)-j h i)≤1*h
      omega
    exact fitt.of_le fun h i=>((S_ h i).group_power (k:=k_ h) rfl rfl (j h i)).ge
  have squares : ∀ᶠ h:ℕ in atTop,∀i,let dim:=(S_ h i).groupWidth (k_ h) (τ*(J_ h+1)) (age h i)+k_ h;dim*dim≤h/2 :=by
    filter_upwards [dyadic_log_room (2*(A*A)) 4] with h bound
    intro i
    let d:=(S_ h i).groupWidth (k_ h) (τ*(J_ h+1)) (age h i)+k_ h
    have first : d≤A*(J_ h+1)^2:=dims h (age h i)
    have second:=Nat.mul_le_mul_left A (Nat.pow_le_pow_left (Nat.add_le_add_right
      (Nat.div_le_self (Nat.log 2 h) (2*B)) 1) 2)
    apply (Nat.le_div_iff_mul_le (by decide : 0<(2:ℕ))).mpr
    calc d*d*2 ≤ ((A*(Nat.log 2 h+1)^2)*(A*(Nat.log 2 h+1)^2))*2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (first.trans second) (first.trans second))
      _ = (2*(A*A))*(Nat.log 2 h+1)^4 :=by ring
      _ ≤ h:=bound
  exact ⟨hosts age (fun h i=>(before h i).trans (Nat.le_succ _)),hosts (fun h i=>age h i+1)
    (fun h i=>Nat.add_le_add_right (before h i) 1),groups age,groups (fun h i=>age h i+1),
    Bounded.pow_of_linear (K:=1) (squares.mono fun h w i=>by simpa only [Nat.one_mul] using (w i).trans (Nat.div_le_self _ _)),
    squares⟩

end Hierarchy.DescentDatedAddressBook

end OAI
