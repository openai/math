import OAI.Hierarchy.DescentPackedMeterReservation
import OAI.Hierarchy.DescentPublicMeterAny
import OAI.Hierarchy.DescentNamedDonorCode
import OAI.Hierarchy.DescentNamedMeterCode

namespace OAI
/-! # The private scalar meter stays in the allocated donor interval -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentPacking.PackedMatch.Local.Stage DescentRawCablePanel DescentHostDegree
open DescentPackedPrivateSum DescentSIMDLookup ProtocolRAM
noncomputable section
variable (d : DonorDate) (payload base header : ℕ)
local notation "m" => lanes payload d.amount
local notation "r" => 2^d.exponent*d.cap
local notation "names" => donorNameBits d.exponent d.degree
local notation "units" => normBits d.cap d.branch d.colors d.padding
local notation "inBits" => bundleBits 3 names units
local notation "short" => 2+units

theorem observation_bounds (key : d.rankExponent=d.exponent) (degree : d.rankDegree=d.degree)
    (live : 0< m) (hasCap : 0< d.cap) :
    base≤d.meterBase payload base ∧ d.meterBase payload base+1+d.hosts*chunks d.groups m≤d.endAddress payload base ∧
      (d.counter payload base header).endAddr≤d.endAddress payload base :=by
  have rank : r>0:=Nat.mul_pos (by positivity) hasCap
  have capBound : r*max inBits (short*11)≤d.amount:=by
    unfold amount
    refine le_trans ?_ (Nat.le_max_left _ _)
    refine le_trans ?_ (Nat.le_max_right _ _)
    simp only [format,key,degree,le_refl]
  have bits:= (Nat.mul_le_mul_left m capBound).trans (lanes_fit payload d.amount)
  have one : inBits*(m*r)≤payload/2:=by
    calc
      _=m*(r*inBits):=by ac_rfl
      _≤ m*(r*max inBits (short*11)):=Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_max_left _ _))
      _≤_:=bits
  have two : short*((m*r)*11)≤payload/2:=by
    calc
      _=m*(r*(short*11)):=by ac_rfl
      _≤ m*(r*max inBits (short*11)):=Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))
      _≤_:=bits
  have areas : d.endAddress payload base=d.meterBase payload base+8*(d.hosts*chunks d.groups m)+2*2^(payload/2)+12:=rfl
  have later : base≤d.meterBase payload base:=by
    unfold meterBase DonorSpace.meterBase DonorSpace.source DonorSpace.dynamicStart
    dsimp only
    omega
  refine ⟨later,by rw [areas]; omega,?_⟩
  change DescentPackedDonorSpace.endAt (d.meterBase payload base) d.hosts (d.groups*2^d.exponent*d.cap) (m*r)
    inBits short≤_
  rw [show d.groups*2^d.exponent*d.cap=d.groups*r by ac_rfl]
  exact DonorSpace.reserved_counter _ _ _ _ _ _ _ _ live rank one two

theorem atDate_observation_bounds {F : Type} [Field F] (G : PoweredGadget F) (S : DescentCompiler.AtomSchedule)
    (gain k i p payload base header : ℕ)
    (live : 0<lanes payload (atDate G S gain k i p).amount) (hasCap : 0<(atDate G S gain k i p).cap) :
    let d:=atDate G S gain k i p
    base≤d.meterBase payload base ∧ d.meterBase payload base+1+d.hosts*chunks d.groups (lanes payload d.amount)≤d.endAddress payload base ∧
      (d.counter payload base header).endAddr≤d.endAddress payload base :=
  observation_bounds (atDate G S gain k i p) payload base header rfl rfl live hasCap
end
end Hierarchy.DescentSixParty.Chronology.DonorDate

end OAI
