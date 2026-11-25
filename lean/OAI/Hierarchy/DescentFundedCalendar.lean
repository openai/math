import OAI.Hierarchy.DescentNamedFundedChart
import OAI.Hierarchy.DescentResetActorCalendar

namespace OAI
/-! # The fixed funded cells of a scheduled reset match the issued GL and roster sizes -/
namespace Hierarchy.DescentNamedFundedChart
open DescentDatedAddressBook DescentSixParty DescentFundedCensus DescentCompiler DescentDenseHostOrder
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable (S : AtomSchedule) (k tail age p f D payload e oldPow n g : ℕ) (calendar : List ℕ)
local notation "Ht" => GroupStage.depthBound D n f g
local notation "prevCap" => ((calendar.take age).prod*256)
local notation "middle" => ResetMiddle.fromCalendar S k tail age p f D payload e oldPow n Ht calendar
local notation "c" => S.groupWidth k tail age

/-- Inputs which the old stage has already normalized to the common lane pitch.
Its pre-normalization paid, signed and presence pitches do not enter the reset. -/
def previous (oldPitch : ℕ) : StageVenueTail.Date :=
  ⟨k,S.hostSize age,S.groupCount age,D,prevCap,S.censusBits p,oldPitch,oldPitch,oldPitch,oldPitch⟩

variable {d : ℕ} (board : NonlinearExpanders.Graph n d)
local notation "old" => previous S k age p D calendar (2^oldPow)
local notation "mixed" => setup old middle
local notation "fund" => shape board old middle f g

theorem earlier_pitch (v : StageVenueTail.Date) (keys : v.k=k) (hosts : v.hosts=S.hostSize age)
    (groups : v.groups=S.groupCount age) (degree : v.degree=D) (cap : v.cap=prevCap)
    (bits : v.paidBits=S.censusBits p) (lanes : v.lanes=2^oldPow) :
    setup v middle=mixed ∧ shape board v middle f g=fund :=by
  constructor <;> simp [setup,shape,operandWidth,previous,keys,hosts,groups,degree,cap,bits,lanes]

theorem axes (batch : e≤c) (base : S.baseGroups=2^tail) (radix : S.radix=2^k) :
    (mixed).high+(mixed).low=c+k ∧ (mixed).cut=c ∧ (mixed).donors=2^k ∧
    2^((mixed).high+(mixed).low)=(mixed).oldGroups*(mixed).blocks ∧
    2^(mixed).low=(mixed).gatherLanes*(mixed).blocks ∧ (mixed).outputLanes*(mixed).donors=2^(mixed).low :=by
  have d : c-e+(e+k)=c+k:=by omega
  have e₁ : (c-e+(e+k))-c=k:=by omega
  have cov:=S.group_power base radix age
  change c-e+(e+k)=c+k ∧ c=c ∧ 2^((c-e+(e+k))-c)=2^k ∧
    2^(c-e+(e+k))=S.groupCount age*2^k ∧ 2^(e+k)=2^e*2^k ∧ 2^e*2^((c-e+(e+k))-c)=2^(e+k)
  simp [d,pow_add,cov]

theorem booked :
    (fund).hosts=S.hostSize age ∧ (fund).groups=2^c ∧ (fund).lanes=2^e ∧ (fund).bits=S.censusBits p ∧
    (fund).jobs=(roster board k Ht).card ∧ (mixed).precision=S.censusBits p := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem shape_at (j : Fin (fund).jobs) :
    shapes board old middle f g j=ActorSetup.shapeAt board k Ht j :=rfl

end
end Hierarchy.DescentNamedFundedChart

end OAI
