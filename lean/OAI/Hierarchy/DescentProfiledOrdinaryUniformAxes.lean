import OAI.Hierarchy.DescentRegisteredOrdinaryGeometry
import OAI.Hierarchy.DescentProfiledOrdinaryOffer

namespace OAI
/-! Uniform exponential bounds for the actual source and recipient axes.
The selected tail and logarithmic divisor affect only the height threshold. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg =>stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "don_" h:arg x:arg =>DonorDate.atDate G (S_ h x) g (k_ h) (x:idx h).slot.age (x:idx h).slot.p

structure RawLimits (h : ℕ) (x : idx h) : Prop where
  oldHost : (S_ h x).hostSize x.slot.age ≤ 2^(4*h)
  newHost : (S_ h x).hostSize (x.slot.age+1) ≤ 2^(4*h)
  oldGroup : (S_ h x).groupCount x.slot.age ≤ 2^h
  newGroup : (S_ h x).groupCount (x.slot.age+1) ≤ 2^h
  blocks : 2^(k_ h) ≤ 2^h
  degree : (don_ h x).degree ≤ 2^h
  wires : (don_ h x).cap ≤ 2^h
  batch : (S_ h x).batch ≤ 2^(6*h)
  matrix : let dim:=(S_ h x).groupWidth (k_ h) (tail τ (J_ h)) x.slot.age+k_ h
    dim*dim ≤ h/2

theorem raw_limits : ∀ᶠ h : ℕ in atTop,∀x : idx h,RawLimits G board op t f g reset τ drift degreeMax B h x :=by
  let sites:=fun h (x:idx h)=>x.slot.sites
  have supply : Bounded sites:=⟨2,Eventually.of_forall fun h x=>by
    simpa only [←pow_mul,Nat.mul_comm h 2] using x.slot.siteLimit⟩
  have all:=schedule_space G t f g reset τ B sites (fun _ _=>0) supply (fun _ _=>Nat.zero_le _)
  have current:=schedule_space G t f g reset τ B sites (fun h x=>x.slot.age) supply (fun _ x=>x.slot.active.le)
  let c:=hostRate t reset
  let a:=capRate G t g
  let C:=20+(c+a+1)*(t+2)
  filter_upwards [all.halfMatrix,current.halfMatrix,dyadic_log_room C 1,
    eventually_ge_atTop (DescentDatedSeedStartup.initialDegreeMax t)] with h zero dated small deg
  intro x
  let S:=S_ h x
  let k:=k_ h
  let tb:=tail τ (J_ h)
  have dim0:=zero x
  let dim:=S.groupWidth k tb 0+k
  change dim*dim ≤ h/2 at dim0
  have short:dim ≤ h:=(Nat.le_mul_self dim).trans (dim0.trans (Nat.div_le_self h 2))
  have sourceDigits:k*(S.length+1) ≤ h:=by
    dsimp only [dim,AtomSchedule.groupWidth,Nat.sub_zero] at short
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have logs:J_ h ≤ Nat.log 2 h:=Nat.div_le_self ..
  have base:C*((J_ h)+1) ≤ h:=(Nat.mul_le_mul_left C (Nat.add_le_add_right logs 1)).trans (by simpa only [pow_one] using small)
  have extra:c*(S.length+1) ≤ h ∧ 11+a*S.length ≤ h:=by
    change c*((t+1)*(J_ h)+1) ≤ h ∧ 11+a*((t+1)*(J_ h)) ≤ h
    dsimp only [C] at base
    constructor <;> nlinarith only [base,Nat.zero_le c,Nat.zero_le a,Nat.zero_le t,
      Nat.zero_le (J_ h),Nat.zero_le (a*t),Nat.zero_le (c*t),Nat.zero_le (a*(J_ h)),
      Nat.zero_le (c*(J_ h)),Nat.zero_le (c*t*(J_ h)),Nat.zero_le (a*t*(J_ h)),Nat.zero_le (t*(J_ h))]
  have groups (i:ℕ):S.groupCount i ≤ 2^h:=by
    rw [←S.group_power (k:=k) (tail:=tb) rfl rfl i]
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    dsimp only [dim,AtomSchedule.groupWidth,Nat.sub_zero] at short ⊢
    have le:=Nat.mul_le_mul_left k (Nat.sub_le S.length i)
    omega
  have hosts (i:ℕ) (age:i ≤ S.length+1):S.hostSize i ≤ 2^(4*h):=by
    change x.slot.sites*(2^c*2^k)^i ≤ _
    rw [←pow_add,←pow_mul,Nat.add_mul]
    have hi : c*i+k*i ≤ 2*h:=by
      have one:=(Nat.mul_le_mul_left c age).trans extra.1
      have two:=(Nat.mul_le_mul_left k age).trans sourceDigits
      omega
    have site:x.slot.sites ≤ 2^(2*h):=by simpa only [←pow_mul,Nat.mul_comm h 2] using x.slot.siteLimit
    calc
      _ ≤ 2^(2*h)*2^(2*h):=Nat.mul_le_mul site (Nat.pow_le_pow_right (by decide) hi)
      _ = _:=by rw [←pow_add];congr 1; omega
  have copy:S.copies ≤ 2^h:=by
    change 2^tb*(2^k)^(S.length+1) ≤ _
    rw [←pow_mul,←pow_add]
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    dsimp only [dim,AtomSchedule.groupWidth,Nat.sub_zero] at short
    rwa [Nat.mul_add,Nat.mul_one,←Nat.add_assoc]
  have halved:=dated x
  refine ⟨hosts _ (by have le:=x.slot.active;change x.slot.age<S.length at le;omega),
    hosts _ (by have le:=x.slot.active;change x.slot.age<S.length at le;omega),groups _,groups _,?_,?_,?_,?_,halved⟩
  · exact Nat.pow_le_pow_right (by decide) ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans sourceDigits)
  · exact (DescentDatedSeedStartup.seed_degree ..).trans (deg.trans (Nat.lt_two_pow_self.le))
  · apply (NativePitch.all_caps G t g (J_ h) x.slot.age).trans
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    change 8+a*S.length ≤ h
    omega
  · have source:x.slot.sites ≤ 2^(2*h):=by simpa only [←pow_mul,Nat.mul_comm h 2] using x.slot.siteLimit
    change ((x.slot.sites*S.copies)*(2^c)^S.length)*2^(11+a*S.length) ≤ _
    rw [←pow_mul]
    have grow:c*S.length ≤ h:=(Nat.mul_le_mul_left c (Nat.le_succ _)).trans extra.1
    calc
      _ ≤ ((2^(2*h)*2^h)*2^h)*2^h:=Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul source copy) (Nat.pow_le_pow_right (by decide) grow))
        (Nat.pow_le_pow_right (by decide) extra.2)
      _ ≤ _:=by simp only [←pow_add];apply Nat.pow_le_pow_right (by decide : 0 < 2);omega

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
