import OAI.Hierarchy.DescentTerminalPublicRows
import OAI.Hierarchy.DescentShellScalarEnvelope
import OAI.Hierarchy.DescentGlobalControlRoom
import OAI.Hierarchy.DescentNativeSocketScale
import OAI.Hierarchy.DescentInitialPackage

namespace OAI
/-! Address counts of the actual purchased terminal shell, including its original public ports. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentResetInvoice
open DescentTerminalGraphVolume DescentDatedAddressBook Catalyst ThreeFlat.Routing Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B n depth C : ℕ)

structure ShellSource (F : Type) [Field F] (height : ℕ) where
  cp : ℕ
  ports : ℕ
  sites : ℕ
  X : Approximation F cp ports
  opened : 10*(X.size+1) ≤ sites
  upper : sites ≤ (2^height)^2

local notation "src_" h:arg => ShellSource F h
local notation "age_" h:arg => Nat.log 2 h/(2*B)
local notation "st_" h:arg x:arg => stageNumbers G t (age_ h) f g reset (ShellSource.sites x) (tail τ (age_ h))
local notation "kb_" h:arg => groupBits t (age_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "bw_" h:arg x:arg => NativeBranch.binLimit (k:=kb_ h) (st_ h x)
local notation "j_" h:arg x:arg => Nat.clog 2 (NativeBranch.localLimit G (st_ h x))
local notation "unit_" h:arg => G.b^(t*(age_ h))*G.b
local notation "q_" h:arg x:arg => 2^(j_ h x)*(unit_ h)
local notation "p_" h:arg x:arg => (bw_ h x)*(h/(16*((q_ h x)*(bw_ h x))))
local notation "pins_" x:arg => Fintype.card (Port (ShellSource.ports x) (ShellSource.X x).width)
local notation "normal_" h:arg x:arg => terminalWireBudget (ShellSource.X x) G (st_ h x) (p_ h x) n depth C f g
local notation "pool_" h:arg x:arg => terminalPool (ShellSource.X x) G (st_ h x) (p_ h x) (q_ h x) (bw_ h x) n depth C f g
local notation "raw_" h:arg x:arg => terminalRawRows (ShellSource.X x) G (st_ h x) (p_ h x) (q_ h x) n depth C f g
local notation "dim_" h:arg x:arg => (st_ h x).groupWidth (kb_ h) (tail τ (age_ h)) 0+kb_ h
local notation "pub_" h:arg x:arg => (pins_ x)*2^((j_ h x)+((dim_ h x)-2*(j_ h x)))

/-- The exponent is chosen before the tail rate and the denominator of the sampled height. -/
theorem uniform_shell_address :
    ∃K : ℕ, ∀τ B : ℕ, ∀ᶠ h : ℕ in atTop, ∀x : src_ h,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset x.sites (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let W:=NativeBranch.binLimit (k:=k) S
      let j:=Nat.clog 2 (NativeBranch.localLimit G S)
      let rest:=S.groupWidth k (tail τ J) 0+k-2*j
      let q:=2^j*(G.b^(t*J)*G.b)
      let p:=W*(h/(16*(q*W)))
      let pool:=terminalPool x.X G S p q W n depth C f g
      S.hostSize S.length+pool+(pins_ x)*2^(j+rest)+(terminalRawRows x.X G S p q n depth C f g+pool)≤2^(K*h) := by
  obtain ⟨K,paid⟩:=shell_numbers_uniform 4
  refine ⟨K,?_⟩
  intro τ B
  let a:=localSocketRate G t g
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let rate:=⌈258*reentryRate depth C+reentryExteriorRate depth C 256 (GroupStage.depthBound (atRound t) n f g)⌉₊
  let hot:=hostRate t reset*(t+1)
  let A:=a+Nat.clog 2 G.b*(t+1)+(τ+κ+4)+hot
  let exponent:=τ+κ*(t+2)
  filter_upwards [paid,dyadic_log_room exponent 2,dyadic_log_room A 1,eventually_ge_atTop rate] with h cap dim limit rateAt
  intro x J S k W j rest q p pool
  let Z:=2^h
  have one : 1≤Z:=Nat.two_pow_pos _
  have widen {i : ℕ} (small : i≤4) : Z^i≤2^(4*h) :=by
    refine (Nat.pow_le_pow_right one small).trans_eq ?_
    dsimp only [Z];rw [←pow_mul,Nat.mul_comm]
  have grow : Z≤2^(4*h) :=by simpa only [pow_one] using widen (show 1≤4 by decide)
  have jh : J≤Nat.log 2 h := Nat.div_le_self ..
  have linear : A*(J+1) ≤ h :=
    (Nat.mul_le_mul_left A (Nat.add_le_add_right jh 1)).trans (by simpa only [pow_one] using limit)
  have scales (r : ℕ) (rr : r≤A) : scale J r≤Z :=
    Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_right (J+1) rr).trans linear)
  have data:=native_socket_scale G t J f g reset x.sites τ
  have bw : W≤Z:=data.2.2.2.2.1.trans (scales _ (by dsimp only [A];omega))
  have grain : q≤Z:=data.2.2.2.2.2.2.1.trans (scales _ (by dsimp only [A];omega))
  have high : 2^j≤Z:=data.2.2.1.trans (scales _ (by dsimp only [A];omega))
  have kFit : k≤κ*(J+1) := groupBits_linear ..
  have stepsFit : S.length+1≤(t+2)*(J+1) :=by
    change (t+1)*J+1≤(t+2)*(J+1)
    nlinarith only [Nat.zero_le t,Nat.zero_le J]
  have wallBits : S.groupWidth k (tail τ J) 0+k≤h := calc
    _ = τ*(J+1)+k*(S.length+1) := by simp only [AtomSchedule.groupWidth,tail,Nat.sub_zero,Nat.mul_succ,Nat.add_assoc]
    _ ≤ τ*(J+1)^2+(κ*(J+1))*((t+2)*(J+1)) :=
      Nat.add_le_add (Nat.mul_le_mul_left τ (by simpa only [pow_two] using Nat.le_mul_self (J+1)))
        (Nat.mul_le_mul kFit stepsFit)
    _ = exponent*(J+1)^2 := by dsimp only [exponent];ring
    _ ≤ exponent*(Nat.log 2 h+1)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ jh) 2)
    _ ≤ h := dim
  have dcopy : 2^(S.groupWidth k (tail τ J) 0+k)≤Z := Nat.pow_le_pow_right (by decide) wallBits
  have copies : S.copies≤Z := by
    convert dcopy using 1
    change 2^(tail τ J)*(2^k)^(S.length+1)=_
    simp only [AtomSchedule.groupWidth,Nat.sub_zero,pow_succ,←pow_mul,←pow_add,Nat.add_assoc]
  have input : p≤Z^2 :=(Nat.mul_le_mul bw ((Nat.div_le_self ..).trans Nat.lt_two_pow_self.le)).trans_eq (pow_two _).symm
  have unit : G.b^(t*J)*G.b≤Z := (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos j)).trans grain
  have first : S.firstWidth G.b p ≤ Z^3 :=by
    rw [AtomSchedule.firstWidth,AtomSchedule.grain_initial,Nat.mul_assoc]
    exact (Nat.mul_le_mul input unit).trans_eq (by ring)
  have thick : S.copies*S.firstWidth G.b p≤Z^4 :=
    (Nat.mul_le_mul copies first).trans_eq (by ring)
  have pub : 2^(j+rest)≤Z^2 := by
    rw [pow_add,pow_two]
    exact Nat.mul_le_mul high ((Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le ..)).trans dcopy)
  have kk : k*S.length≤h := by
    dsimp only [AtomSchedule.groupWidth,Nat.sub_zero] at wallBits
    omega
  have hh : S.hostGain*S.length≤h := by
    have factor := (Nat.mul_le_mul_right (J+1) (show hot≤A by dsimp only [A];omega)).trans linear
    change hostRate t reset*((t+1)*J)≤h
    dsimp only [hot] at factor
    nlinarith only [factor,Nat.zero_le (hostRate t reset*(t+1))]
  have hpub : S.hostSize S.length ≤ 2^(4*h) := by
    change x.sites*(2^S.hostGain*2^k)^S.length≤_
    rw [←pow_add,←pow_mul,Nat.add_mul]
    have blob : 2^(S.hostGain*S.length+k*S.length) ≤ Z^2 := by
      rw [pow_add,pow_two]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hh) (Nat.pow_le_pow_right (by decide) kk)
    exact ((Nat.mul_le_mul x.upper blob).trans_eq (by change Z^2*Z^2=Z^4;ring)).trans (widen (by decide : 4≤4))
  have steps : S.epochPower≤Z:=Nat.pow_le_pow_right (by decide) (jh.trans (Nat.log_le_self ..))
  have ep : (pins_ x)≤x.sites:= (Nat.le_add_left ..).trans ((DescentInitialHost.«initialize» x.X).2.1.trans x.opened)
  let v:ShellNumbers:=⟨S.epochPower,x.sites,S.copies*S.firstWidth G.b p,pins_ x,rate,S.hostSize S.length,W,p,q,2^(j+rest)⟩
  exact cap v ⟨steps.trans grow,x.upper.trans (widen (by decide)),thick.trans (widen le_rfl),
    ep.trans (x.upper.trans (widen (by decide))),rateAt.trans (Nat.lt_two_pow_self.le.trans grow),
    hpub,bw.trans grow,input.trans (widen (by decide)),grain.trans grow,pub.trans (widen (by decide))⟩

/-- All five row registers of the calibrated shell have the same word-size exponent. -/
theorem shell_address :
    ∃K : ℕ, ∀ᶠ h : ℕ in atTop, ∀x : src_ h,
      (st_ h x).hostSize (st_ h x).length + (pool_ h x) + (pub_ h x) +
        ((raw_ h x)+(pool_ h x)) ≤ 2^(K*h) := by
  obtain ⟨K,good⟩:=uniform_shell_address G t f g reset n depth C
  exact ⟨K,good τ B⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
