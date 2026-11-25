import OAI.Hierarchy.DescentMeterIntervalNumbers
import OAI.Hierarchy.DescentNamedMeterCode
import OAI.Hierarchy.DescentPublicMeterAny

namespace OAI
/-! # The paid public counter fits between the rotation end and the next native allocation -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentSIMDLookup DescentRawCablePanel DescentHostDegree DescentPacking.PackedMatch.Local.Stage.Dated
open DescentCompiler
noncomputable section

theorem counter_between (d : DonorDate) (payload floor header : ℕ)
    (names : donorNameBits d.rankExponent d.rankDegree=donorNameBits d.exponent d.degree) :
    let meter:=d.counter payload floor header
    floor≤ meter.base ∧ meter.base< meter.endAddr ∧ meter.endAddr≤d.endAddress payload floor :=by
  intro meter
  let units:=normBits d.cap d.branch d.colors d.padding
  let input:=bundleBits 3 (donorNameBits d.exponent d.degree) units
  let short:=2+units
  let seats:=2^d.exponent*d.cap
  let full:=max input (short*11)
  let M:=lanes payload d.amount
  let words:=d.hosts*chunks d.groups M
  have factor : seats*full≤d.amount:=by
    unfold amount
    simp only [format,names]
    exact (le_max_right ..).trans (le_max_left ..)
  have lower : floor≤ meter.base:=by
    change floor≤DonorSpace.meterBase floor _ _ _
    unfold DonorSpace.meterBase DonorSpace.source DonorSpace.dynamicStart
    dsimp only
    omega
  have mid : meter.base< meter.endAddr:=DescentPackedDonorSpace.above ..
  refine ⟨lower,mid,?_⟩
  change DescentPackedDonorSpace.endAt meter.base d.hosts (d.groups*2^d.exponent*d.cap) (M*seats) input short≤
    meter.base+8*words+2*2^(payload/2)+12
  rw [Nat.mul_assoc d.groups]
  exact DescentPackedDonorSpace.grouped_end meter.base d.hosts d.groups seats input short d.amount payload factor

theorem dated_counter_between {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
    (gain k i p payload floor header : ℕ) :
    let date:=atDate G S gain k i p
    let meter:=date.counter payload floor header
    floor≤ meter.base ∧ meter.base< meter.endAddr ∧ meter.endAddr≤date.endAddress payload floor :=
  counter_between _ _ _ _ rfl

end
end Hierarchy.DescentSixParty.Chronology.DonorDate

end OAI
