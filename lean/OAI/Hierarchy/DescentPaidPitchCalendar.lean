import OAI.Hierarchy.DescentNamedPrefixPitch

namespace OAI
/-! # A fixed public purchase for the seed, both ordinary banks, and every reset bank -/
namespace Hierarchy.DescentSixParty.PitchCalendar
open DescentCompiler DescentCompiler.TerminalScale Chronology DescentDatedAddressBook
open DescentDatedSeedStartup PhysicalReset Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset drift driftR degreeMax quota ratio : ℕ)
local notation "seed" => selected_seed_pitch_room G op t f g reset drift degreeMax quota
local notation "price₀" => (NativePitch.FundedBase.public_rate G t f g reset).choose
local notation "spend" => 44*argumentDigitRate G t f g reset driftR price₀
local notation "rr" => registeredRoleRate G t f g reset
local notation "ar" => returnLaneRate G t f g reset spend
local notation "dr" => allDensityRate G board op t f g reset (maximumDegree (t+1))
def argumentRate := max (seed).choose (max ar dr)
def roleRate := max (seed).choose (max rr dr)

def threshold (τ : ℕ) :=
  1+(seed).choose_spec.choose τ+(incomingRate G t f g reset+2)+ar+rr+
    2*degreeRate G board op t f g reset (maximumDegree (t+1))+
    2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))

structure Purchased (τ B h : ℕ) : Prop where
  old : ArgumentCalendar G op t f g reset τ B drift driftR degreeMax h
  returned : ReturnCalendar G t f g reset driftR spend τ B ratio h
  resetPitch : DensityCalendar G board op t f g reset τ (maximumDegree (t+1)) drift B degreeMax h
  roleWidth : scale (Nat.log 2 h/(2*B)) rr≤h
  initial :
    let J:=Nat.log 2 h/(2*B)
    ∀M degree base field wire hist : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(t*J)*G.b)
    let bin:=NativeBranch.binLimit (k:=k) S
    let p:=bin*(h/(16*(q*bin)))
    let l:=selectedLayout G S h k (tail τ J) g p drift degree f quota base field wire hist
    ∀cp nP (X : Catalyst.Approximation F cp nP) (R H : ℕ),degree≤degreeMax →
      (DatePorts.initial G op X R l k H (S.groupCount 0) h (S.grainAt G.b p 0)).ArchivePitchRoom
        (S.groupCount 0) h (scale J (seed).choose) (scale J (seed).choose)

theorem eventually_purchased (τ B : ℕ) (openTail : 0<τ)
    (fund : threshold G board op t f g reset drift driftR degreeMax quota τ≤B) :
    ∀ᶠ h : ℕ in atTop,Purchased G board op t f g reset drift driftR degreeMax quota ratio τ B h :=by
  unfold threshold at fund
  have pos : 0<B:=by omega
  have seedBuy : (seed).choose_spec.choose τ≤B:=by omega
  have incomingBuy : incomingRate G t f g reset+2≤B:=by omega
  have argBuy : ar<B:=by omega
  have roleBuy : rr<B:=by omega
  have degreeBuy : 2*degreeRate G board op t f g reset (maximumDegree (t+1))≤B:=by omega
  have tailBuy : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B:=by omega
  have branch : G.b≤2^(capRate G t g):=by
    have base : G.b≤capRate G t g:=by unfold capRate;omega
    exact base.trans (Nat.lt_two_pow_self.le)
  filter_upwards [eventual_argument_width G op t f g reset τ B drift driftR degreeMax pos,
    eventual_registered_tail G t f g reset driftR spend τ B ratio 0 op drift incomingBuy argBuy branch tailBuy,
    eventual_density_calendar G board op t f g reset τ (maximumDegree (t+1)) drift B degreeMax pos degreeBuy branch,
    eventually_role_payload G t f g reset B roleBuy,(seed).choose_spec.choose_spec τ B openTail seedBuy]
    with h old ret reset_ role first
  exact ⟨old,ret,reset_,(Nat.le_mul_of_pos_left _ (by decide : 0<2)).trans role,first⟩

end
end Hierarchy.DescentSixParty.PitchCalendar

end OAI
